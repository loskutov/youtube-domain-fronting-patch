package app.sni_patch.patches.shared.misc.sni

import app.morphe.patcher.patch.PatchException
import app.morphe.patcher.patch.ResourcePatchBuilder
import app.morphe.patcher.patch.resourcePatch
import app.morphe.patcher.patch.stringOption
import java.io.File
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.abs

private const val ARM64_DIR = "lib/arm64-v8a"
private const val DEFAULT_FORCED_SNI_HOST = "kek.bdn.dev"
private const val HTTPS_PORT = 443
private const val HOST_PORT_PAIR_SIZE = 0x20
private const val HOST_PORT_PAIR_PORT_OFFSET = 0x00
private const val HOST_PORT_PAIR_HOST_OFFSET = 0x08
private const val SHORT_STRING_SIZE_OFFSET = HOST_PORT_PAIR_HOST_OFFSET + 0x17
private const val MAX_SHORT_STRING_HOST_LENGTH = 22
private const val ORIGINAL_SNI_HOST = "i.ytimg.com"
private const val TRAMPOLINE_CODE_SIZE = 0x48
private const val TRAMPOLINE_LITERAL_OFFSET = TRAMPOLINE_CODE_SIZE
private const val TRAMPOLINE_SYNTHETIC_HOST_PORT_PAIR_OFFSET = TRAMPOLINE_LITERAL_OFFSET + Long.SIZE_BYTES
private const val TRAMPOLINE_PAYLOAD_SIZE = TRAMPOLINE_SYNTHETIC_HOST_PORT_PAIR_OFFSET + HOST_PORT_PAIR_SIZE
private const val ARM64_CONDITION_NE = 0x1
private val HOSTNAME_REGEX = Regex("^[A-Za-z0-9-]+(\\.[A-Za-z0-9-]+)+$")

// Source-level context:
// - SSLConnectJob::DoSSLConnect() first completes the nested TransportConnectJob
//   and obtains a connected StreamSocket.
// - It then calls CreateSSLClientSocket(..., std::move(nested_socket_),
//   params_->host_and_port(), ssl_config).
//
// This is the clean boundary between the lower transport endpoint and the TLS
// authentication hostname. The fingerprint below matches the call-site tail
// where x3 is loaded with params_->host_and_port(). We only replace that x3
// argument with a synthetic HostPortPair stored in an RX cave; the underlying
// connected stream socket keeps using the original endpoint.
private val TLS_HOST_ARGUMENT_FINGERPRINT_BYTES = byteArrayOf(
    0x43, 0x61, 0x00, 0x91.toByte(), // add x3, x10, #0x18
    0x08, 0x00, 0x40, 0xf9.toByte(), // ldr x8, [x0]
    0x09, 0x11, 0x80.toByte(), 0xb9.toByte(), // ldrsw x9, [x8, #0x10]
    0x08, 0x01, 0x09, 0x8b.toByte(), // add x8, x8, x9
    0x00, 0x01, 0x3f, 0xd6.toByte(), // blr x8
)

private const val TLS_HOST_ARGUMENT_INSTRUCTION_OFFSET = 0
private const val BRK_MASK = 0xffe0001f.toInt()
private const val BRK_OPCODE = 0xd4200000.toInt()

private fun ByteArray.findAll(needle: ByteArray): List<Int> {
    if (needle.isEmpty() || size < needle.size) return emptyList()

    val matches = mutableListOf<Int>()
    for (index in 0..(size - needle.size)) {
        if (this[index] != needle[0]) continue

        var matched = true
        for (i in 1 until needle.size) {
            if (this[index + i] != needle[i]) {
                matched = false
                break
            }
        }

        if (matched) {
            matches += index
        }
    }

    return matches
}

private fun alignUp(value: Int, alignment: Int): Int {
    return (value + alignment - 1) and -alignment
}

private fun ByteArray.readIntLE(offset: Int): Int {
    return ByteBuffer.wrap(this, offset, Int.SIZE_BYTES)
        .order(ByteOrder.LITTLE_ENDIAN)
        .int
}

private fun decodeDirectBranchTarget(
    instruction: Int,
    instructionFileOffset: Int,
    loadSegments: List<ElfLoadSegment>,
): Int? {
    // Check if instruction offset is within a PT_LOAD segment
    val offsetLong = instructionFileOffset.toLong()
    val isInLoadSegment = loadSegments.any { segment ->
        offsetLong >= segment.fileOffset && offsetLong < segment.fileOffset + segment.fileSize
    }
    if (!isInLoadSegment) return null

    val instructionVirtualAddress = fileOffsetToVirtualAddress(instructionFileOffset, loadSegments)

    val targetVirtualAddress = when {
        instruction ushr 26 == 0b000101 || instruction ushr 26 == 0b100101 -> {
            var imm26 = instruction and 0x03ffffff
            if ((imm26 and (1 shl 25)) != 0) {
                imm26 = imm26 or (-1 shl 26)
            }
            instructionVirtualAddress + (imm26.toLong() shl 2)
        }

        instruction and 0xff000010.toInt() == 0x54000000 -> {
            var imm19 = (instruction ushr 5) and 0x7ffff
            if ((imm19 and (1 shl 18)) != 0) {
                imm19 = imm19 or (-1 shl 19)
            }
            instructionVirtualAddress + (imm19.toLong() shl 2)
        }

        instruction and 0x7e000000 == 0x34000000 -> {
            var imm19 = (instruction ushr 5) and 0x7ffff
            if ((imm19 and (1 shl 18)) != 0) {
                imm19 = imm19 or (-1 shl 19)
            }
            instructionVirtualAddress + (imm19.toLong() shl 2)
        }

        instruction and 0x7e000000 == 0x36000000 -> {
            var imm14 = (instruction ushr 5) and 0x3fff
            if ((imm14 and (1 shl 13)) != 0) {
                imm14 = imm14 or (-1 shl 14)
            }
            instructionVirtualAddress + (imm14.toLong() shl 2)
        }

        else -> return null
    }

    return virtualAddressToFileOffset(targetVirtualAddress, loadSegments)
}

private fun collectDirectBranchTargets(
    bytes: ByteArray,
    loadSegments: List<ElfLoadSegment>,
): Set<Int> {
    val targets = mutableSetOf<Int>()
    for (offset in 0..(bytes.size - Int.SIZE_BYTES) step Int.SIZE_BYTES) {
        decodeDirectBranchTarget(bytes.readIntLE(offset), offset, loadSegments)?.let(targets::add)
    }
    return targets
}

private fun isUnusedCaveWord(instruction: Int): Boolean {
    return instruction == 0 ||
            instruction == 0xd503201f.toInt() ||
            instruction and BRK_MASK == BRK_OPCODE
}

private fun findTrampolineCave(
    bytes: ByteArray,
    patchOffset: Int,
    loadSegments: List<ElfLoadSegment>,
): Int {
    val branchTargets = collectDirectBranchTargets(bytes, loadSegments)
    val patchVirtualAddress = fileOffsetToVirtualAddress(patchOffset, loadSegments)

    for (segment in loadSegments.filter { it.isExecutable }) {
        val segmentStart = alignUp(segment.fileOffset.toInt(), Int.SIZE_BYTES)
        val segmentEnd = (segment.fileOffset + segment.fileSize).toInt() - TRAMPOLINE_PAYLOAD_SIZE
        if (segmentStart > segmentEnd) continue

        for (offset in segmentStart..segmentEnd step Int.SIZE_BYTES) {
            val caveOffset = alignUp(offset, Long.SIZE_BYTES)
            if (caveOffset > segmentEnd) continue

            val caveVirtualAddress = fileOffsetToVirtualAddress(caveOffset, loadSegments)
            val branchDelta = caveVirtualAddress - patchVirtualAddress
            if ((branchDelta and 0x3L) != 0L || abs(branchDelta shr 2) >= (1 shl 25)) continue

            val caveRange = caveOffset until caveOffset + TRAMPOLINE_PAYLOAD_SIZE
            if (branchTargets.any { it in caveRange }) continue

            val isUnused = caveRange.step(Int.SIZE_BYTES).all { wordOffset ->
                isUnusedCaveWord(bytes.readIntLE(wordOffset))
            }
            if (!isUnused) continue

            println("DEBUG: Found executable trampoline cave at 0x${caveOffset.toString(16)}")
            return caveOffset
        }
    }

    throw PatchException("No suitable executable RX cave found for conditional SNI trampoline")
}

private fun buildSyntheticHostPortPair(host: String): ByteArray {
    require(host.length <= MAX_SHORT_STRING_HOST_LENGTH) {
        "Host '$host' is too long for libc++ short-string HostPortPair storage"
    }

    return ByteArray(HOST_PORT_PAIR_SIZE).also { bytes ->
        val hostBytes = host.encodeToByteArray()
        hostBytes.copyInto(bytes, destinationOffset = HOST_PORT_PAIR_HOST_OFFSET)
        bytes[HOST_PORT_PAIR_HOST_OFFSET + hostBytes.size] = 0
        bytes[SHORT_STRING_SIZE_OFFSET] = hostBytes.size.toByte()
        bytes[HOST_PORT_PAIR_PORT_OFFSET] = (HTTPS_PORT and 0xff).toByte()
        bytes[HOST_PORT_PAIR_PORT_OFFSET + 1] = ((HTTPS_PORT ushr 8) and 0xff).toByte()
    }
}

private fun ByteArray.writeInstruction(offset: Int, instruction: Int) {
    instruction.toLittleEndianBytes().copyInto(this, destinationOffset = offset)
}

private fun buildConditionalSniTrampoline(
    caveVirtualAddress: Long,
    returnVirtualAddress: Long,
    syntheticHostPortPair: ByteArray,
): ByteArray {
    val originalHostBytes = ORIGINAL_SNI_HOST.encodeToByteArray()
    check(originalHostBytes.size == 11) { "Unexpected ORIGINAL_SNI_HOST length" }

    val payload = ByteArray(TRAMPOLINE_PAYLOAD_SIZE)
    val forcedPathOffset = 0x40
    val forcedPathVirtualAddress = caveVirtualAddress + forcedPathOffset
    val literalVirtualAddress = caveVirtualAddress + TRAMPOLINE_LITERAL_OFFSET
    val syntheticHostPortPairVirtualAddress = caveVirtualAddress + TRAMPOLINE_SYNTHETIC_HOST_PORT_PAIR_OFFSET

    fun instructionVirtualAddress(offset: Int) = caveVirtualAddress + offset

    // x10 is already the SSLConnectJob params pointer at the original call-site.
    // x3 must contain params_->host_and_port() unless we choose the synthetic SNI pair.
    payload.writeInstruction(0x00, encodeAddImmediate(3, 10, 0x18))
    payload.writeInstruction(0x04, encodeLdrUnsignedImmediate(11, 3, SHORT_STRING_SIZE_OFFSET, sizeBytes = 1))
    payload.writeInstruction(0x08, encodeCmpImmediate(11, originalHostBytes.size, is64Bit = false))
    payload.writeInstruction(0x0c, encodeConditionalBranch(instructionVirtualAddress(0x0c), forcedPathVirtualAddress, ARM64_CONDITION_NE))
    payload.writeInstruction(0x10, encodeLdrUnsignedImmediate(11, 3, HOST_PORT_PAIR_HOST_OFFSET, sizeBytes = 8))
    payload.writeInstruction(0x14, encodeLdrLiteral(12, instructionVirtualAddress(0x14), literalVirtualAddress, is64Bit = true))
    payload.writeInstruction(0x18, encodeEorShiftedRegister(11, 11, 12, is64Bit = true))
    payload.writeInstruction(0x1c, encodeCbnz(11, instructionVirtualAddress(0x1c), forcedPathVirtualAddress, is64Bit = true))
    payload.writeInstruction(0x20, encodeLdrUnsignedImmediate(11, 3, HOST_PORT_PAIR_HOST_OFFSET + 8, sizeBytes = 2))
    payload.writeInstruction(0x24, encodeMovz(12, 0x6f63, is64Bit = false))
    payload.writeInstruction(0x28, encodeCmpShiftedRegister(11, 12, is64Bit = false))
    payload.writeInstruction(0x2c, encodeConditionalBranch(instructionVirtualAddress(0x2c), forcedPathVirtualAddress, ARM64_CONDITION_NE))
    payload.writeInstruction(0x30, encodeLdrUnsignedImmediate(11, 3, HOST_PORT_PAIR_HOST_OFFSET + 10, sizeBytes = 1))
    payload.writeInstruction(0x34, encodeCmpImmediate(11, 'm'.code, is64Bit = false))
    payload.writeInstruction(0x38, encodeConditionalBranch(instructionVirtualAddress(0x38), forcedPathVirtualAddress, ARM64_CONDITION_NE))
    payload.writeInstruction(0x3c, encodeB(instructionVirtualAddress(0x3c), returnVirtualAddress))
    payload.writeInstruction(0x40, encodeAdr(3, instructionVirtualAddress(0x40), syntheticHostPortPairVirtualAddress))
    payload.writeInstruction(0x44, encodeB(instructionVirtualAddress(0x44), returnVirtualAddress))

    originalHostBytes.copyInto(payload, destinationOffset = TRAMPOLINE_LITERAL_OFFSET, endIndex = 8)
    syntheticHostPortPair.copyInto(payload, destinationOffset = TRAMPOLINE_SYNTHETIC_HOST_PORT_PAIR_OFFSET)
    return payload
}

private fun chooseCronetLibrary(arm64Dir: File): File? {
    val candidates = arm64Dir.listFiles()
        ?.filter { file ->
            file.isFile && file.name.startsWith("libcronet") && file.name.endsWith(".so")
        }
        ?.sortedBy { it.name }
        .orEmpty()

    return when (candidates.size) {
        0 -> null
        1 -> candidates.single()
        else -> throw PatchException(
            "Expected exactly one libcronet*.so in '$ARM64_DIR', found: " +
                    candidates.joinToString { it.name }
        )
    }
}

@Suppress("unused")
val forceCronetSniPatchShared = forceCronetSniPatch {
    // No specific compatibility - potentially universal for apps using Cronet
}

internal fun forceCronetSniPatch(
    name: String = "Force Cronet SNI (arm64)",
    block: ResourcePatchBuilder.() -> Unit,
) = resourcePatch(
    name = name,
    description = "Patches bundled arm64 libcronet so TLS SNI is forced to a configurable hostname in " +
            "the SSLClientSocket path. URL and HTTP Host remain unchanged.",
    default = false,
) {
    block()

    val forcedSniHost by stringOption(
        key = "forcedSniHost",
        default = DEFAULT_FORCED_SNI_HOST,
        title = "Forced SNI hostname",
        description = "Hostname written into libcronet and used by the SSLClientSocket path for TLS SNI.",
        required = true,
    ) {
        it != null && HOSTNAME_REGEX.matches(it)
    }

    execute {
        val forcedSniHostValue = forcedSniHost!!.trim()
        if (forcedSniHostValue.length > MAX_SHORT_STRING_HOST_LENGTH) {
            throw PatchException(
                "Forced SNI host '$forcedSniHostValue' is too long. " +
                        "Maximum supported length is $MAX_SHORT_STRING_HOST_LENGTH characters."
            )
        }

        val arm64Dir = get(ARM64_DIR)
            ?: throw PatchException("Missing '$ARM64_DIR' in target APK")

        val cronetLib = chooseCronetLibrary(arm64Dir)
            ?: throw PatchException("No libcronet*.so found in '$ARM64_DIR'")

        val bytes = cronetLib.readBytes()
        val loadSegments = parseElfLoadSegments(bytes)
        val expected = TLS_HOST_ARGUMENT_FINGERPRINT_BYTES

        val patchOffsets = bytes.findAll(expected)
        if (patchOffsets.isEmpty()) {
            throw PatchException("TLS host argument fingerprint not found in ${cronetLib.name}.")
        }
        if (patchOffsets.size > 1) {
            println("WARNING: TLS host argument fingerprint matched multiple locations: " +
                    patchOffsets.joinToString { "0x${it.toString(16)}" })
            println("Using first match: 0x${patchOffsets.first().toString(16)}")
        }

        val patchOffset = patchOffsets.first() + TLS_HOST_ARGUMENT_INSTRUCTION_OFFSET
        println("DEBUG: Using patch offset: 0x${patchOffset.toString(16)}")

        val caveOffset = findTrampolineCave(
            bytes = bytes,
            patchOffset = patchOffset,
            loadSegments = loadSegments,
        )
        println("DEBUG: Found cave at offset: 0x${caveOffset.toString(16)}")

        val caveVirtualAddress = fileOffsetToVirtualAddress(caveOffset, loadSegments)
        val patchVirtualAddress = fileOffsetToVirtualAddress(patchOffset, loadSegments)

        val syntheticHostPortPair = buildSyntheticHostPortPair(forcedSniHostValue)
        val trampoline = buildConditionalSniTrampoline(
            caveVirtualAddress = caveVirtualAddress,
            returnVirtualAddress = patchVirtualAddress + Int.SIZE_BYTES,
            syntheticHostPortPair = syntheticHostPortPair,
        )
        println(
            "DEBUG: Placing conditional SNI trampoline at 0x${caveOffset.toString(16)}; " +
                    "leaving original SNI for $ORIGINAL_SNI_HOST and forcing $forcedSniHostValue otherwise"
        )
        trampoline.copyInto(bytes, destinationOffset = caveOffset)

        // Replace `add x3, x10, #0x18` (`params_->host_and_port()`) at the
        // SSLConnectJob boundary with a branch to a trampoline. The trampoline
        // keeps `i.ytimg.com` on the original HostPortPair and redirects all
        // other TLS hostnames to the synthetic pair. The nested StreamSocket has
        // already connected to the original endpoint, so the transport endpoint
        // and HTTP Host remain unchanged.
        val branchInstruction = encodeB(
            instructionVirtualAddress = patchVirtualAddress,
            targetVirtualAddress = caveVirtualAddress,
        )
        println("DEBUG: Patching instruction at 0x${patchOffset.toString(16)}: 0x${branchInstruction.toString(16)}")
        branchInstruction.toLittleEndianBytes().copyInto(bytes, destinationOffset = patchOffset)

        cronetLib.writeBytes(bytes)
    }
}
