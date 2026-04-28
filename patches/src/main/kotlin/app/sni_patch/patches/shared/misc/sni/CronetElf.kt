package app.sni_patch.patches.shared.misc.sni

import app.morphe.patcher.patch.PatchException
import java.nio.ByteBuffer
import java.nio.ByteOrder

internal data class ElfLoadSegment(
    val fileOffset: Long,
    val fileSize: Long,
    val virtualAddress: Long,
    val flags: Int,
)

internal val ElfLoadSegment.isExecutable: Boolean
    get() = flags and 0x1 != 0

internal fun parseElfLoadSegments(bytes: ByteArray): List<ElfLoadSegment> {
    if (bytes.size < 0x40) {
        throw PatchException("Target library is too small to be a valid ELF64 binary")
    }

    if (bytes[0] != 0x7f.toByte() || bytes[1] != 'E'.code.toByte() ||
        bytes[2] != 'L'.code.toByte() || bytes[3] != 'F'.code.toByte() ||
        bytes[4].toInt() != 2 || bytes[5].toInt() != 1
    ) {
        throw PatchException("Target library is not a little-endian ELF64 binary")
    }

    val bb = ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN)
    val programHeaderOffset = bb.getLong(0x20)
    val programHeaderEntrySize = bb.getShort(0x36).toInt() and 0xffff
    val programHeaderCount = bb.getShort(0x38).toInt() and 0xffff

    if (programHeaderOffset < 0 || programHeaderEntrySize <= 0 || programHeaderCount <= 0) {
        throw PatchException("ELF program header table is missing or malformed")
    }

    val segments = mutableListOf<ElfLoadSegment>()
    repeat(programHeaderCount) { index ->
        val entryOffset = programHeaderOffset + index.toLong() * programHeaderEntrySize
        if (entryOffset < 0 || entryOffset + programHeaderEntrySize > bytes.size.toLong()) {
            throw PatchException("ELF program header entry $index is out of bounds")
        }

        val base = entryOffset.toInt()
        val type = bb.getInt(base)
        if (type != 1) return@repeat

        val flags = bb.getInt(base + 0x04)
        val fileOffset = bb.getLong(base + 0x08)
        val virtualAddress = bb.getLong(base + 0x10)
        val fileSize = bb.getLong(base + 0x20)
        if (fileSize > 0) {
            segments += ElfLoadSegment(
                fileOffset = fileOffset,
                fileSize = fileSize,
                virtualAddress = virtualAddress,
                flags = flags,
            )
        }
    }

    if (segments.isEmpty()) {
        throw PatchException("ELF binary does not contain any PT_LOAD segments")
    }

    return segments
}

internal fun fileOffsetToVirtualAddress(
    fileOffset: Int,
    segments: List<ElfLoadSegment>,
): Long {
    val offset = fileOffset.toLong()
    val segment = segments.firstOrNull { candidate ->
        offset >= candidate.fileOffset && offset < candidate.fileOffset + candidate.fileSize
    } ?: throw PatchException("File offset 0x${fileOffset.toString(16)} is not covered by any PT_LOAD segment")

    return segment.virtualAddress + (offset - segment.fileOffset)
}

internal fun virtualAddressToFileOffset(
    virtualAddress: Long,
    segments: List<ElfLoadSegment>,
): Int? {
    val segment = segments.firstOrNull { candidate ->
        virtualAddress >= candidate.virtualAddress &&
                virtualAddress < candidate.virtualAddress + candidate.fileSize
    } ?: return null

    val offset = segment.fileOffset + (virtualAddress - segment.virtualAddress)
    return offset.toInt()
}

internal fun encodeAdr(
    register: Int,
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
): Int {
    require(register in 0..31) { "Invalid ADR register: $register" }

    val delta = targetVirtualAddress - instructionVirtualAddress
    val minDelta = -(1 shl 20)
    val maxDelta = (1 shl 20) - 1
    if (delta < minDelta || delta > maxDelta) {
        throw PatchException("ADR target delta out of range: $delta")
    }

    val imm21 = delta and 0x1fffff
    val immlo = (imm21 and 0x3).toInt()
    val immhi = ((imm21 shr 2) and 0x7ffff).toInt()

    return 0x10000000 or (immlo shl 29) or (immhi shl 5) or register
}

internal fun encodeAdrp(
    register: Int,
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
): Int {
    require(register in 0..31) { "Invalid ADRP register: $register" }

    val instructionPage = instructionVirtualAddress and -0x1000L
    val targetPage = targetVirtualAddress and -0x1000L
    val deltaPages = (targetPage - instructionPage) shr 12

    val minDelta = -(1 shl 20)
    val maxDelta = (1 shl 20) - 1
    if (deltaPages < minDelta || deltaPages > maxDelta) {
        throw PatchException("ADRP page delta out of range: $deltaPages")
    }

    val imm21 = deltaPages and 0x1fffff
    val immlo = (imm21 and 0x3).toInt()
    val immhi = ((imm21 shr 2) and 0x7ffff).toInt()

    return 0x90000000.toInt() or (immlo shl 29) or (immhi shl 5) or register
}

internal fun encodeAddImmediate(
    destinationRegister: Int,
    sourceRegister: Int,
    immediate: Int,
): Int {
    require(destinationRegister in 0..31) { "Invalid ADD destination register: $destinationRegister" }
    require(sourceRegister in 0..31) { "Invalid ADD source register: $sourceRegister" }
    require(immediate in 0..0xfff) { "ADD immediate out of range: $immediate" }

    return 0x91000000.toInt() or
            (immediate shl 10) or
            (sourceRegister shl 5) or
            destinationRegister
}

internal fun encodeMovz(
    register: Int,
    immediate: Int,
    is64Bit: Boolean = false,
): Int {
    require(register in 0..31) { "Invalid MOVZ register: $register" }
    require(immediate in 0..0xffff) { "MOVZ immediate out of range: $immediate" }

    val base = if (is64Bit) 0xD2800000.toInt() else 0x52800000
    return base or (immediate shl 5) or register
}

internal fun encodeB(
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
): Int {
    val delta = targetVirtualAddress - instructionVirtualAddress
    if ((delta and 0x3L) != 0L) {
        throw PatchException("B target delta is not instruction-aligned: $delta")
    }

    val imm26 = delta shr 2
    val minDelta = -(1 shl 25)
    val maxDelta = (1 shl 25) - 1
    if (imm26 < minDelta || imm26 > maxDelta) {
        throw PatchException("B target delta out of range: $delta")
    }

    return 0x14000000 or (imm26.toInt() and 0x03ffffff)
}

internal fun encodeConditionalBranch(
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
    condition: Int,
): Int {
    require(condition in 0..0xf) { "Invalid condition: $condition" }

    val delta = targetVirtualAddress - instructionVirtualAddress
    if ((delta and 0x3L) != 0L) {
        throw PatchException("B.cond target delta is not instruction-aligned: $delta")
    }

    val imm19 = delta shr 2
    val minDelta = -(1 shl 18)
    val maxDelta = (1 shl 18) - 1
    if (imm19 < minDelta || imm19 > maxDelta) {
        throw PatchException("B.cond target delta out of range: $delta")
    }

    return 0x54000000 or ((imm19.toInt() and 0x7ffff) shl 5) or condition
}

internal fun encodeLdrUnsignedImmediate(
    destinationRegister: Int,
    baseRegister: Int,
    immediate: Int,
    sizeBytes: Int,
): Int {
    require(destinationRegister in 0..31) { "Invalid LDR destination register: $destinationRegister" }
    require(baseRegister in 0..31) { "Invalid LDR base register: $baseRegister" }
    require(immediate >= 0) { "LDR immediate out of range: $immediate" }
    require(sizeBytes == 1 || sizeBytes == 2 || sizeBytes == 4 || sizeBytes == 8) {
        "Invalid LDR size: $sizeBytes"
    }
    require(immediate % sizeBytes == 0) { "LDR immediate is not scaled-aligned: $immediate" }

    val scaledImmediate = immediate / sizeBytes
    require(scaledImmediate in 0..0xfff) { "LDR immediate out of range: $immediate" }

    val base = when (sizeBytes) {
        1 -> 0x39400000
        2 -> 0x79400000
        4 -> 0xb9400000.toInt()
        else -> 0xf9400000.toInt()
    }

    return base or (scaledImmediate shl 10) or (baseRegister shl 5) or destinationRegister
}

internal fun encodeLdrLiteral(
    destinationRegister: Int,
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
    is64Bit: Boolean,
): Int {
    require(destinationRegister in 0..31) { "Invalid LDR literal destination register: $destinationRegister" }

    val delta = targetVirtualAddress - instructionVirtualAddress
    if ((delta and 0x3L) != 0L) {
        throw PatchException("LDR literal target delta is not instruction-aligned: $delta")
    }

    val imm19 = delta shr 2
    val minDelta = -(1 shl 18)
    val maxDelta = (1 shl 18) - 1
    if (imm19 < minDelta || imm19 > maxDelta) {
        throw PatchException("LDR literal target delta out of range: $delta")
    }

    val base = if (is64Bit) 0x58000000 else 0x18000000
    return base or ((imm19.toInt() and 0x7ffff) shl 5) or destinationRegister
}

internal fun encodeEorShiftedRegister(
    destinationRegister: Int,
    leftRegister: Int,
    rightRegister: Int,
    is64Bit: Boolean,
): Int {
    require(destinationRegister in 0..31) { "Invalid EOR destination register: $destinationRegister" }
    require(leftRegister in 0..31) { "Invalid EOR left register: $leftRegister" }
    require(rightRegister in 0..31) { "Invalid EOR right register: $rightRegister" }

    val base = if (is64Bit) 0xca000000.toInt() else 0x4a000000
    return base or (rightRegister shl 16) or (leftRegister shl 5) or destinationRegister
}

internal fun encodeCbnz(
    register: Int,
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
    is64Bit: Boolean,
): Int {
    require(register in 0..31) { "Invalid CBNZ register: $register" }

    val delta = targetVirtualAddress - instructionVirtualAddress
    if ((delta and 0x3L) != 0L) {
        throw PatchException("CBNZ target delta is not instruction-aligned: $delta")
    }

    val imm19 = delta shr 2
    val minDelta = -(1 shl 18)
    val maxDelta = (1 shl 18) - 1
    if (imm19 < minDelta || imm19 > maxDelta) {
        throw PatchException("CBNZ target delta out of range: $delta")
    }

    val base = if (is64Bit) 0xb5000000.toInt() else 0x35000000
    return base or ((imm19.toInt() and 0x7ffff) shl 5) or register
}

internal fun encodeCmpImmediate(
    register: Int,
    immediate: Int,
    is64Bit: Boolean,
): Int {
    require(register in 0..31) { "Invalid CMP register: $register" }
    require(immediate in 0..0xfff) { "CMP immediate out of range: $immediate" }

    val base = if (is64Bit) 0xf100001f.toInt() else 0x7100001f
    return base or (immediate shl 10) or (register shl 5)
}

internal fun encodeCmpShiftedRegister(
    leftRegister: Int,
    rightRegister: Int,
    is64Bit: Boolean,
): Int {
    require(leftRegister in 0..31) { "Invalid CMP left register: $leftRegister" }
    require(rightRegister in 0..31) { "Invalid CMP right register: $rightRegister" }

    val base = if (is64Bit) 0xeb00001f.toInt() else 0x6b00001f
    return base or (rightRegister shl 16) or (leftRegister shl 5)
}

internal fun decodeBlTargetVirtualAddress(
    bytes: ByteArray,
    instructionFileOffset: Int,
    segments: List<ElfLoadSegment>,
): Long? {
    if (instructionFileOffset < 0 || instructionFileOffset + 4 > bytes.size) return null

    val instruction = ByteBuffer.wrap(bytes, instructionFileOffset, 4)
        .order(ByteOrder.LITTLE_ENDIAN)
        .int
    val opcode = instruction ushr 26
    if (opcode != 0b100101) return null

    var imm26 = instruction and 0x03ffffff
    if ((imm26 and (1 shl 25)) != 0) {
        imm26 = imm26 or (-1 shl 26)
    }

    val instructionVirtualAddress = fileOffsetToVirtualAddress(instructionFileOffset, segments)
    return instructionVirtualAddress + (imm26.toLong() shl 2)
}

internal fun encodeBl(
    instructionVirtualAddress: Long,
    targetVirtualAddress: Long,
): Int {
    val delta = targetVirtualAddress - instructionVirtualAddress
    if ((delta and 0x3L) != 0L) {
        throw PatchException("BL target delta is not instruction-aligned: $delta")
    }

    val imm26 = delta shr 2
    val minDelta = -(1 shl 25)
    val maxDelta = (1 shl 25) - 1
    if (imm26 < minDelta || imm26 > maxDelta) {
        throw PatchException("BL target delta out of range: $delta")
    }

    return 0x94000000.toInt() or (imm26.toInt() and 0x03ffffff)
}

internal fun Int.toLittleEndianBytes(): ByteArray {
    return byteArrayOf(
        (this and 0xff).toByte(),
        ((this ushr 8) and 0xff).toByte(),
        ((this ushr 16) and 0xff).toByte(),
        ((this ushr 24) and 0xff).toByte(),
    )
}
