#[cfg(target_arch = "x86")]
pub use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
pub use core::arch::x86_64::*;

pub use self::__m256i as m256i;

#[inline]
pub fn mm256i(i: i8) -> m256i {
    unsafe {
        _mm256_setr_epi8(
            i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i, i,
            i, i, i,
        )
    }
}

/// Create a value of `m256i` from the slice of bytes.
///
/// # Safety
/// This function guarantees the safety only if the length of `s` is greater than or equal to `i + 32`.
#[inline(always)]
pub unsafe fn u8_to_m256i(s: &[u8], i: usize) -> m256i {
    _mm256_setr_epi8(
        *s.as_ptr().add(i) as i8,
        *s.as_ptr().add(i + 1) as i8,
        *s.as_ptr().add(i + 2) as i8,
        *s.as_ptr().add(i + 3) as i8,
        *s.as_ptr().add(i + 4) as i8,
        *s.as_ptr().add(i + 5) as i8,
        *s.as_ptr().add(i + 6) as i8,
        *s.as_ptr().add(i + 7) as i8,
        *s.as_ptr().add(i + 8) as i8,
        *s.as_ptr().add(i + 9) as i8,
        *s.as_ptr().add(i + 10) as i8,
        *s.as_ptr().add(i + 11) as i8,
        *s.as_ptr().add(i + 12) as i8,
        *s.as_ptr().add(i + 13) as i8,
        *s.as_ptr().add(i + 14) as i8,
        *s.as_ptr().add(i + 15) as i8,
        *s.as_ptr().add(i + 16) as i8,
        *s.as_ptr().add(i + 17) as i8,
        *s.as_ptr().add(i + 18) as i8,
        *s.as_ptr().add(i + 19) as i8,
        *s.as_ptr().add(i + 20) as i8,
        *s.as_ptr().add(i + 21) as i8,
        *s.as_ptr().add(i + 22) as i8,
        *s.as_ptr().add(i + 23) as i8,
        *s.as_ptr().add(i + 24) as i8,
        *s.as_ptr().add(i + 25) as i8,
        *s.as_ptr().add(i + 26) as i8,
        *s.as_ptr().add(i + 27) as i8,
        *s.as_ptr().add(i + 28) as i8,
        *s.as_ptr().add(i + 29) as i8,
        *s.as_ptr().add(i + 30) as i8,
        *s.as_ptr().add(i + 31) as i8,
    )
}

#[inline]
pub unsafe fn u8_to_m256i_rest(s: &[u8], i: usize) -> m256i {
    match s.len() - i {
        31 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            *s.as_ptr().add(i + 26) as i8,
            *s.as_ptr().add(i + 27) as i8,
            *s.as_ptr().add(i + 28) as i8,
            *s.as_ptr().add(i + 29) as i8,
            *s.as_ptr().add(i + 30) as i8,
            0,
        ),
        30 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            *s.as_ptr().add(i + 26) as i8,
            *s.as_ptr().add(i + 27) as i8,
            *s.as_ptr().add(i + 28) as i8,
            *s.as_ptr().add(i + 29) as i8,
            0,
            0,
        ),
        29 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            *s.as_ptr().add(i + 26) as i8,
            *s.as_ptr().add(i + 27) as i8,
            *s.as_ptr().add(i + 28) as i8,
            0,
            0,
            0,
        ),
        28 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            *s.as_ptr().add(i + 26) as i8,
            *s.as_ptr().add(i + 27) as i8,
            0,
            0,
            0,
            0,
        ),
        27 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            *s.as_ptr().add(i + 26) as i8,
            0,
            0,
            0,
            0,
            0,
        ),
        26 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            *s.as_ptr().add(i + 25) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        25 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            *s.as_ptr().add(i + 24) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        24 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            *s.as_ptr().add(i + 23) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        23 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            *s.as_ptr().add(i + 22) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        22 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            *s.as_ptr().add(i + 21) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        21 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            *s.as_ptr().add(i + 20) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        20 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            *s.as_ptr().add(i + 19) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        19 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            *s.as_ptr().add(i + 18) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        18 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            *s.as_ptr().add(i + 17) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        17 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            *s.as_ptr().add(i + 16) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        16 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            *s.as_ptr().add(i + 15) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        15 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            *s.as_ptr().add(i + 14) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        14 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            *s.as_ptr().add(i + 13) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        13 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            *s.as_ptr().add(i + 12) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        12 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            *s.as_ptr().add(i + 11) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        11 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            *s.as_ptr().add(i + 10) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        10 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            *s.as_ptr().add(i + 9) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        9 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            *s.as_ptr().add(i + 8) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        8 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            *s.as_ptr().add(i + 7) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        7 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            *s.as_ptr().add(i + 6) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        6 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            *s.as_ptr().add(i + 5) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        5 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            *s.as_ptr().add(i + 4) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        4 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            *s.as_ptr().add(i + 3) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        3 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            *s.as_ptr().add(i + 2) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        2 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            *s.as_ptr().add(i + 1) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        1 => _mm256_setr_epi8(
            *s.as_ptr().add(i) as i8,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ),
        _ => _mm256_setr_epi8(
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ),
    }
}
