use crate::{NumCmp, U128_BOUND_IN_F64};
use derive_deref_rs::Deref;
use std::cmp::Ordering;

const BYTES_BOUND_IN_F32: usize = f32::MAX_EXP as usize / u8::BITS as usize;
const BYTES_BOUND_IN_F64: usize = f64::MAX_EXP as usize / u8::BITS as usize;
const U64_BYTES: usize = (u64::BITS / u8::BITS) as usize;
const U64_MANTISSA_BYTES: usize = 53 / u8::BITS as usize + 1;
const U128_BYTES: usize = (u128::BITS / u8::BITS) as usize;

/// A big unsigned integer type.
/// big endian, high front, low back
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BigUint<'a> {
    data: &'a [u8],
}
impl<'a> From<&'a [u8]> for BigUint<'a> {
    #[inline]
    fn from(value: &'a [u8]) -> Self {
        BigUint::new(value)
    }
}
impl<'a> BigUint<'a> {
    #[inline]
    pub const fn new(value: &'a [u8]) -> Self {
        let i = Self::leading_zeros(value);
        let (_, data) = unsafe { value.split_at_unchecked(i) };
        BigUint { data }
    }
    #[inline]
    pub const fn leading_zeros(value: &[u8]) -> usize {
        let mut i = 0;
        while i < value.len() {
            if value[i] != 0 {
                break;
            }
            i += 1;
        }
        i
    }
    /// Get the length of the underlying data.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }
    #[inline]
    pub fn as_slice(&self) -> &'a [u8] {
        &self.data
    }
    #[inline]
    pub fn bits(&self) -> usize {
        self.data.len() << 3
    }
    #[inline]
    pub fn high_bits(&self) -> usize {
        if self.data.len() == 0 {
            return 0;
        }
        self.bits() - self.data[0].leading_zeros() as usize
    }
    #[inline]
    fn to_u64(&self) -> u64 {
        let mut data = [0; U64_BYTES];
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.data.as_ptr(),
                data.as_mut_ptr(),
                self.data.len().min(U64_BYTES),
            )
        };
        u64::from_be_bytes(data)
    }
    #[inline]
    fn to_u128(&self) -> u128 {
        let mut data = [0; U128_BYTES];
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.data.as_ptr(),
                data.as_mut_ptr()
                    .add(U128_BYTES.saturating_sub(self.data.len())),
                self.data.len().min(U128_BYTES),
            )
        };
        u128::from_be_bytes(data)
    }
    fn finite_positive_f32_cmp(&self, other: f32) -> Ordering {
        if self.data.len() == 0 {
            return if other == 0.0 {
                Ordering::Equal
            } else {
                Ordering::Less
            };
        } else if self.data.len() > BYTES_BOUND_IN_F32 {
            return Ordering::Greater;
        }
        let int = other.trunc();
        (self.to_u128(), int)
            .partial_cmp(&(int as u128, other))
            .unwrap()
    }
    fn finite_positive_f64_cmp(&self, other: f64) -> Ordering {
        if self.data.len() == 0 {
            return if other == 0.0 {
                Ordering::Equal
            } else {
                Ordering::Less
            };
        } else if self.data.len() <= U128_BYTES {
            if other > U128_BOUND_IN_F64 {
                return Ordering::Less;
            }
            let int = other.trunc();
            return (self.to_u128(), int)
                .partial_cmp(&(int as u128, other))
                .unwrap();
        } else if self.data.len() > BYTES_BOUND_IN_F64 {
            return Ordering::Greater;
        } else if other < 1.0 {
            return Ordering::Greater;
        }

        // 将浮点数分解为 IEEE 754 表示
        // 指数全 0 为 非规范数（非常接近 0 的极小值，精度降低），已由 f >= 1.0 排除
        let bits = other.to_bits();
        // 11 位指数
        let exponent = ((bits >> 52) & 0x7FF) as i32;
        // 52 位尾数
        let mantissa = bits & 0x000F_FFFF_FFFF_FFFF;
        // 计算实际的有效数字, 规格化数: 1 + 尾数
        let significand = (1 << 52) | mantissa;

        // 实际指数 = 指数 - 1023 - 52
        let exp_power = exponent - 1023 - 52; // E - 52

        // 根据指数偏移方向处理
        if exp_power >= 0 {
            // 情况1: 指数偏移 >= 0 (f 表示为整数) 整数值为 significand << exp_power;

            // 获得大整数的最高位
            let left_bits = self.high_bits();

            // 获得浮点数的最高位
            let right_bits =
                exp_power as usize + (u64::BITS - significand.leading_zeros()) as usize;

            // 比较最高位
            if left_bits > right_bits {
                return Ordering::Greater;
            } else if left_bits < right_bits {
                return Ordering::Less;
            }
            // 取高64位区间比较
            let left = self.to_u64();
            let right = significand << (exp_power as usize + u64::BITS as usize - self.bits());
            if left < right {
                return Ordering::Less;
            } else if left > right {
                return Ordering::Greater;
            }
            // 如果高64位区间都相等，则继续检查大数剩余部分，如果有剩余，则大数大
            for d in &self.data[U64_BYTES..] {
                if *d != 0 {
                    return Ordering::Greater;
                }
            }
            Ordering::Equal
        } else {
            // 情况2: 指数偏移 < 0 (f 表示为分数), 分子为 significand, 分母为 2^(-exp_power)
            // 必定小于 2^53
            if self.data.len() > U64_MANTISSA_BYTES {
                return Ordering::Greater;
            }

            // 优化: 如果分母 > 分子，则 f < 1，但已由 f >= 1.0 排除

            // 比较 self.to_u64() * 分母 和 significand (分子)
            if let Some(left) = self.to_u64().checked_shl((-exp_power) as u32) {
                left.cmp(&significand)
            } else {
                // 如果溢出，则必然大于
                Ordering::Greater
            }
        }
    }
    #[inline]
    fn bytes_cmp<const N: usize>(self, other: &[u8; N]) -> Ordering {
        if self.data.len() > N {
            return Ordering::Greater;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).cmp(&(other.len(), other));
        }
        self.data.cmp(other)
    }
    #[inline]
    fn bytes_eq<const N: usize>(self, other: &[u8; N]) -> bool {
        if self.data.len() > N {
            return false;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).eq(&(other.len(), other));
        }
        self.data.eq(other)
    }

    #[inline]
    fn bytes_ne<const N: usize>(self, other: &[u8; N]) -> bool {
        !self.bytes_eq(other)
    }

    #[inline]
    fn bytes_lt<const N: usize>(self, other: &[u8; N]) -> bool {
        if self.data.len() > N {
            return false;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).lt(&(other.len(), other));
        }
        self.data.lt(other)
    }

    #[inline]
    fn bytes_gt<const N: usize>(self, other: &[u8; N]) -> bool {
        if self.data.len() > N {
            return true;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).gt(&(other.len(), other));
        }
        self.data.gt(other)
    }

    #[inline]
    fn bytes_le<const N: usize>(self, other: &[u8; N]) -> bool {
        if self.data.len() > N {
            return false;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).le(&(other.len(), other));
        }
        self.data.le(other)
    }

    #[inline]
    fn bytes_ge<const N: usize>(self, other: &[u8; N]) -> bool {
        if self.data.len() > N {
            return true;
        }
        if self.data.len() < N {
            let i = Self::leading_zeros(other);
            let (_, other) = unsafe { other.split_at_unchecked(i) };
            return (self.data.len(), self.data).ge(&(other.len(), other));
        }
        self.data.ge(other)
    }
}
impl<'a> Ord for BigUint<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (self.data.len(), self.data).cmp(&(other.data.len(), other.data))
    }
}
impl<'a> PartialOrd for BigUint<'a> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl NumCmp<f32> for BigUint<'_> {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: f32) -> &'static str {
        "strategy, BigUint vs f32"
    }

    #[inline]
    fn num_cmp(self, other: f32) -> Ordering {
        if other < 0.0 {
            return Ordering::Greater;
        } else if !other.is_finite() {
            return Ordering::Less;
        }
        self.finite_positive_f32_cmp(other)
    }

    #[inline]
    fn num_eq(self, other: f32) -> bool {
        if other < 0.0 || !other.is_finite() {
            return false;
        }
        self.finite_positive_f32_cmp(other).is_eq()
    }

    #[inline]
    fn num_ne(self, other: f32) -> bool {
        !self.num_eq(other)
    }

    #[inline]
    fn num_lt(self, other: f32) -> bool {
        if other < 0.0 {
            return false;
        } else if !other.is_finite() {
            return true;
        }
        self.finite_positive_f32_cmp(other).is_lt()
    }

    #[inline]
    fn num_gt(self, other: f32) -> bool {
        if other < 0.0 {
            return true;
        } else if !other.is_finite() {
            return false;
        }
        self.finite_positive_f32_cmp(other).is_gt()
    }

    #[inline]
    fn num_le(self, other: f32) -> bool {
        if other < 0.0 {
            return false;
        } else if !other.is_finite() {
            return true;
        }
        self.finite_positive_f32_cmp(other).is_le()
    }

    #[inline]
    fn num_ge(self, other: f32) -> bool {
        if other < 0.0 {
            return true;
        } else if !other.is_finite() {
            return false;
        }
        self.finite_positive_f32_cmp(other).is_ge()
    }
}

impl NumCmp<BigUint<'_>> for f32 {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: BigUint<'_>) -> &'static str {
        "strategy, f32 vs BigUint"
    }

    #[inline]
    fn num_cmp(self, other: BigUint<'_>) -> Ordering {
        other.num_cmp(self).reverse()
    }

    #[inline]
    fn num_eq(self, other: BigUint<'_>) -> bool {
        other.num_eq(self)
    }

    #[inline]
    fn num_ne(self, other: BigUint<'_>) -> bool {
        other.num_ne(self)
    }

    #[inline]
    fn num_lt(self, other: BigUint<'_>) -> bool {
        other.num_gt(self)
    }

    #[inline]
    fn num_gt(self, other: BigUint<'_>) -> bool {
        other.num_lt(self)
    }

    #[inline]
    fn num_le(self, other: BigUint<'_>) -> bool {
        other.num_ge(self)
    }

    #[inline]
    fn num_ge(self, other: BigUint<'_>) -> bool {
        other.num_le(self)
    }
}

impl NumCmp<f64> for BigUint<'_> {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: f64) -> &'static str {
        "strategy, BigUint vs f64"
    }

    #[inline]
    fn num_cmp(self, other: f64) -> Ordering {
        if other < 0.0 {
            return Ordering::Greater;
        } else if !other.is_finite() {
            return Ordering::Less;
        }
        self.finite_positive_f64_cmp(other)
    }

    #[inline]
    fn num_eq(self, other: f64) -> bool {
        self.num_cmp(other).is_eq()
    }

    #[inline]
    fn num_ne(self, other: f64) -> bool {
        self.num_cmp(other).is_ne()
    }

    #[inline]
    fn num_lt(self, other: f64) -> bool {
        self.num_cmp(other).is_lt()
    }

    #[inline]
    fn num_gt(self, other: f64) -> bool {
        self.num_cmp(other).is_gt()
    }

    #[inline]
    fn num_le(self, other: f64) -> bool {
        self.num_cmp(other).is_lt()
    }

    #[inline]
    fn num_ge(self, other: f64) -> bool {
        self.num_cmp(other).is_ge()
    }
}

impl NumCmp<BigUint<'_>> for f64 {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: BigUint<'_>) -> &'static str {
        "strategy, f64 vs BigUint"
    }

    #[inline]
    fn num_cmp(self, other: BigUint<'_>) -> Ordering {
        other.num_cmp(self).reverse()
    }

    #[inline]
    fn num_eq(self, other: BigUint<'_>) -> bool {
        other.num_eq(self)
    }

    #[inline]
    fn num_ne(self, other: BigUint<'_>) -> bool {
        other.num_ne(self)
    }

    #[inline]
    fn num_lt(self, other: BigUint<'_>) -> bool {
        other.num_gt(self)
    }

    #[inline]
    fn num_gt(self, other: BigUint<'_>) -> bool {
        other.num_lt(self)
    }

    #[inline]
    fn num_le(self, other: BigUint<'_>) -> bool {
        other.num_ge(self)
    }

    #[inline]
    fn num_ge(self, other: BigUint<'_>) -> bool {
        other.num_le(self)
    }
}

/// A big signed integer type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deref)]
pub struct BigInt<'a> {
    #[deref]
    biguint: BigUint<'a>,
    sign_positive: bool,
}
impl<'a> BigInt<'a> {
    /// Create a new `BigInt` from a BigUint and sign.
    #[inline]
    pub const fn new(biguint: BigUint<'a>, sign_positive: bool) -> Self {
        BigInt {
            biguint,
            sign_positive,
        }
    }
    /// Get the sign.
    #[inline]
    pub fn is_sign_positive(&self) -> bool {
        self.sign_positive
    }
    /// Set the sign.
    #[inline]
    pub fn set_sign_positive(&mut self, sign_positive: bool) {
        self.sign_positive = sign_positive;
    }
}
impl<'a> From<BigUint<'a>> for BigInt<'a> {
    #[inline]
    fn from(value: BigUint<'a>) -> Self {
        BigInt::new(value, true)
    }
}
impl<'a> Ord for BigInt<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.biguint.cmp(&other.biguint),
            (false, true) => Ordering::Less,
            (true, false) => Ordering::Greater,
            (false, false) => other.biguint.cmp(&self.biguint),
        }
    }
}
impl<'a> PartialOrd for BigInt<'a> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl NumCmp<f32> for BigInt<'_> {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: f32) -> &'static str {
        "strategy, BigInt vs f32"
    }

    #[inline]
    fn num_cmp(self, other: f32) -> Ordering {
        if other.is_nan() || other == f32::INFINITY {
            return Ordering::Less;
        }
        if other == f32::NEG_INFINITY {
            return Ordering::Greater;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other),
            (false, true) => Ordering::Less,
            (true, false) => Ordering::Greater,
            (false, false) => self.finite_positive_f32_cmp(-other).reverse(),
        }
    }

    #[inline]
    fn num_eq(self, other: f32) -> bool {
        if !other.is_finite() {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other).is_eq(),
            (false, false) => self.finite_positive_f32_cmp(-other).is_eq(),
            _ => false,
        }
    }

    #[inline]
    fn num_ne(self, other: f32) -> bool {
        !self.num_eq(other)
    }

    #[inline]
    fn num_lt(self, other: f32) -> bool {
        if other.is_nan() || other == f32::INFINITY {
            return true;
        }
        if other == f32::NEG_INFINITY {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other).is_lt(),
            (false, true) => true,
            (true, false) => false,
            (false, false) => self.finite_positive_f32_cmp(-other).is_gt(),
        }
    }

    #[inline]
    fn num_gt(self, other: f32) -> bool {
        if other.is_nan() || other == f32::INFINITY {
            return false;
        }
        if other == f32::NEG_INFINITY {
            return true;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other).is_gt(),
            (false, true) => false,
            (true, false) => true,
            (false, false) => self.finite_positive_f32_cmp(-other).is_lt(),
        }
    }

    #[inline]
    fn num_le(self, other: f32) -> bool {
        if other.is_nan() || other == f32::INFINITY {
            return true;
        }
        if other == f32::NEG_INFINITY {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other).is_le(),
            (false, true) => true,
            (true, false) => false,
            (false, false) => self.finite_positive_f32_cmp(-other).is_ge(),
        }
    }

    #[inline]
    fn num_ge(self, other: f32) -> bool {
        if other.is_nan() || other == f32::INFINITY {
            return false;
        }
        if other == f32::NEG_INFINITY {
            return true;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f32_cmp(other).is_ge(),
            (false, true) => false,
            (true, false) => true,
            (false, false) => self.finite_positive_f32_cmp(-other).is_le(),
        }
    }
}

impl NumCmp<BigInt<'_>> for f32 {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: BigInt<'_>) -> &'static str {
        "strategy, f32 vs BigInt"
    }

    #[inline]
    fn num_cmp(self, other: BigInt<'_>) -> Ordering {
        other.num_cmp(self).reverse()
    }

    #[inline]
    fn num_eq(self, other: BigInt<'_>) -> bool {
        other.num_eq(self)
    }

    #[inline]
    fn num_ne(self, other: BigInt<'_>) -> bool {
        other.num_ne(self)
    }

    #[inline]
    fn num_lt(self, other: BigInt<'_>) -> bool {
        other.num_gt(self)
    }

    #[inline]
    fn num_gt(self, other: BigInt<'_>) -> bool {
        other.num_lt(self)
    }

    #[inline]
    fn num_le(self, other: BigInt<'_>) -> bool {
        other.num_ge(self)
    }

    #[inline]
    fn num_ge(self, other: BigInt<'_>) -> bool {
        other.num_le(self)
    }
}

impl NumCmp<f64> for BigInt<'_> {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: f64) -> &'static str {
        "strategy, BigInt vs f32"
    }

    #[inline]
    fn num_cmp(self, other: f64) -> Ordering {
        if other.is_nan() || other == f64::INFINITY {
            return Ordering::Less;
        }
        if other == f64::NEG_INFINITY {
            return Ordering::Greater;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other),
            (false, true) => Ordering::Less,
            (true, false) => Ordering::Greater,
            (false, false) => self.finite_positive_f64_cmp(-other).reverse(),
        }
    }

    #[inline]
    fn num_eq(self, other: f64) -> bool {
        if !other.is_finite() {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other).is_eq(),
            (false, false) => self.finite_positive_f64_cmp(-other).is_eq(),
            _ => false,
        }
    }

    #[inline]
    fn num_ne(self, other: f64) -> bool {
        !self.num_eq(other)
    }

    #[inline]
    fn num_lt(self, other: f64) -> bool {
        if other.is_nan() || other == f64::INFINITY {
            return true;
        }
        if other == f64::NEG_INFINITY {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other).is_lt(),
            (false, true) => true,
            (true, false) => false,
            (false, false) => self.finite_positive_f64_cmp(-other).is_gt(),
        }
    }

    #[inline]
    fn num_gt(self, other: f64) -> bool {
        if other.is_nan() || other == f64::INFINITY {
            return false;
        }
        if other == f64::NEG_INFINITY {
            return true;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other).is_gt(),
            (false, true) => false,
            (true, false) => true,
            (false, false) => self.finite_positive_f64_cmp(-other).is_lt(),
        }
    }

    #[inline]
    fn num_le(self, other: f64) -> bool {
        if other.is_nan() || other == f64::INFINITY {
            return true;
        }
        if other == f64::NEG_INFINITY {
            return false;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other).is_le(),
            (false, true) => true,
            (true, false) => false,
            (false, false) => self.finite_positive_f64_cmp(-other).is_ge(),
        }
    }

    #[inline]
    fn num_ge(self, other: f64) -> bool {
        if other.is_nan() || other == f64::INFINITY {
            return false;
        }
        if other == f64::NEG_INFINITY {
            return true;
        }
        match (self.sign_positive, other.is_sign_positive()) {
            (true, true) => self.finite_positive_f64_cmp(other).is_ge(),
            (false, true) => false,
            (true, false) => true,
            (false, false) => self.finite_positive_f64_cmp(-other).is_le(),
        }
    }
}

impl NumCmp<BigInt<'_>> for f64 {
    #[cfg(test)]
    fn num_cmp_strategy(self, _other: BigInt<'_>) -> &'static str {
        "strategy, f64 vs BigInt"
    }

    #[inline]
    fn num_cmp(self, other: BigInt<'_>) -> Ordering {
        other.num_cmp(self).reverse()
    }

    #[inline]
    fn num_eq(self, other: BigInt<'_>) -> bool {
        other.num_eq(self)
    }

    #[inline]
    fn num_ne(self, other: BigInt<'_>) -> bool {
        other.num_ne(self)
    }

    #[inline]
    fn num_lt(self, other: BigInt<'_>) -> bool {
        other.num_gt(self)
    }

    #[inline]
    fn num_gt(self, other: BigInt<'_>) -> bool {
        other.num_lt(self)
    }

    #[inline]
    fn num_le(self, other: BigInt<'_>) -> bool {
        other.num_ge(self)
    }

    #[inline]
    fn num_ge(self, other: BigInt<'_>) -> bool {
        other.num_le(self)
    }
}

macro_rules! impl_for_uint_types_with_biguint {
    ($($uint:ty;)*) => ($(
        impl NumCmp<$uint> for BigUint<'_> {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: $uint) -> &'static str {
                "strategy, BigUint vs uint"
            }

            #[inline]
            fn num_cmp(self, other: $uint) -> Ordering {
                self.bytes_cmp(&other.to_be_bytes())
            }

            #[inline]
            fn num_eq(self, other: $uint) -> bool {
                self.bytes_eq(&other.to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: $uint) -> bool {
                self.bytes_ne(&other.to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: $uint) -> bool {
                self.bytes_lt(&other.to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: $uint) -> bool {
                self.bytes_gt(&other.to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: $uint) -> bool {
                self.bytes_le(&other.to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: $uint) -> bool {
                self.bytes_ge(&other.to_be_bytes())
            }
        }

        impl NumCmp<BigUint<'_>> for $uint {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: BigUint<'_>) -> &'static str {
                "strategy, uint vs BigUint"
            }

            #[inline]
            fn num_cmp(self, other: BigUint<'_>) -> Ordering {
                other.bytes_cmp(&self.to_be_bytes()).reverse()
            }

            #[inline]
            fn num_eq(self, other: BigUint<'_>) -> bool {
                other.bytes_eq(&self.to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: BigUint<'_>) -> bool {
                other.bytes_ne(&self.to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: BigUint<'_>) -> bool {
                other.bytes_gt(&self.to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: BigUint<'_>) -> bool {
                other.bytes_lt(&self.to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: BigUint<'_>) -> bool {
                other.bytes_ge(&self.to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: BigUint<'_>) -> bool {
                other.bytes_le(&self.to_be_bytes())
            }
        }
    )*);
}

macro_rules! impl_for_int_types_with_biguint {
    ($($int:ty, $big:ty;)*) => ($(
        impl NumCmp<$int> for BigUint<'_> {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: $int) -> &'static str {
                "strategy, BigUint vs int"
            }

            #[inline]
            fn num_cmp(self, other: $int) -> Ordering {
                if other < 0 {
                    return Ordering::Greater
                }
                self.bytes_cmp(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_eq(self, other: $int) -> bool {
                if other < 0 {
                    return false
                }
                self.bytes_eq(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: $int) -> bool {
                if other < 0 {
                    return true
                }
                self.bytes_ne(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: $int) -> bool {
                if other < 0 {
                    return false
                }
                self.bytes_lt(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: $int) -> bool {
                if other < 0 {
                    return true
                }
                self.bytes_gt(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: $int) -> bool {
                if other < 0 {
                    return false
                }
                self.bytes_le(&(other as $big).to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: $int) -> bool {
                if other < 0 {
                    return true
                }
                self.bytes_ge(&(other as $big).to_be_bytes())
            }
        }

        impl NumCmp<BigUint<'_>> for $int {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: BigUint<'_>) -> &'static str {
                "strategy, int vs BigUint"
            }

            #[inline]
            fn num_cmp(self, other: BigUint<'_>) -> Ordering {
                if self < 0 {
                    return Ordering::Less
                }
                other.bytes_cmp(&(self as $big).to_be_bytes()).reverse()
            }

            #[inline]
            fn num_eq(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return false
                }
                other.bytes_eq(&(self as $big).to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return true
                }
                other.bytes_ne(&(self as $big).to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return true
                }
                other.bytes_gt(&(self as $big).to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return false
                }
                other.bytes_lt(&(self as $big).to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return true
                }
                other.bytes_ge(&(self as $big).to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: BigUint<'_>) -> bool {
                if self < 0 {
                    return false
                }
                other.bytes_le(&(self as $big).to_be_bytes())
            }
        }
    )*);
}

macro_rules! impl_for_uint_types_with_bigint {
    ($($uint:ty;)*) => ($(
        impl NumCmp<$uint> for BigInt<'_> {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: $uint) -> &'static str {
                "strategy, BigInt vs uint"
            }

            #[inline]
            fn num_cmp(self, other: $uint) -> Ordering {
                if !self.sign_positive {
                    return Ordering::Less
                }
                self.bytes_cmp(&other.to_be_bytes())
            }

            #[inline]
            fn num_eq(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return false
                }
                self.bytes_eq(&other.to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return true
                }
                self.bytes_ne(&other.to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return true
                }
                self.bytes_lt(&other.to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return false
                }
                self.bytes_gt(&other.to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return true
                }
                self.bytes_le(&other.to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: $uint) -> bool {
                if !self.sign_positive {
                    return false
                }
                self.bytes_ge(&other.to_be_bytes())
            }
        }

        impl NumCmp<BigInt<'_>> for $uint {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: BigInt<'_>) -> &'static str {
                "strategy, uint vs BigInt"
            }

            #[inline]
            fn num_cmp(self, other: BigInt<'_>) -> Ordering {
                if !other.sign_positive {
                    return Ordering::Greater
                }
                other.bytes_cmp(&self.to_be_bytes()).reverse()
            }

            #[inline]
            fn num_eq(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return false
                }
                other.bytes_eq(&self.to_be_bytes())
            }

            #[inline]
            fn num_ne(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return true
                }
                other.bytes_ne(&self.to_be_bytes())
            }

            #[inline]
            fn num_lt(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return false
                }
                other.bytes_gt(&self.to_be_bytes())
            }

            #[inline]
            fn num_gt(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return true
                }
                other.bytes_lt(&self.to_be_bytes())
            }

            #[inline]
            fn num_le(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return false
                }
                other.bytes_ge(&self.to_be_bytes())
            }

            #[inline]
            fn num_ge(self, other: BigInt<'_>) -> bool {
                if !other.sign_positive {
                    return true
                }
                other.bytes_le(&self.to_be_bytes())
            }
        }
    )*);
}

macro_rules! impl_for_int_types_with_bigint {
    ($($int:ty, $big:ty;)*) => ($(
        impl NumCmp<$int> for BigInt<'_> {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: $int) -> &'static str {
                "strategy, BigInt vs int"
            }

            #[inline]
            fn num_cmp(self, other: $int) -> Ordering {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_cmp(&(other as $big).to_be_bytes()),
                    (false, true) => Ordering::Less,
                    (true, false) => Ordering::Greater,
                    (false, false) => self.bytes_cmp(&(other as $big).wrapping_neg().to_be_bytes()).reverse(),
                }
            }

            #[inline]
            fn num_eq(self, other: $int) -> bool {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_eq(&(other as $big).to_be_bytes()),
                    (false, false) => self.bytes_eq(&(other as $big).wrapping_neg().to_be_bytes()),
                    _ => false,
                }
            }

            #[inline]
            fn num_ne(self, other: $int) -> bool {
                !self.num_eq(other)
            }

            #[inline]
            fn num_lt(self, other: $int) -> bool {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_lt(&(other as $big).to_be_bytes()),
                    (false, true) => true,
                    (true, false) => false,
                    (false, false) => self.bytes_gt(&(other as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_gt(self, other: $int) -> bool {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_gt(&(other as $big).to_be_bytes()),
                    (false, true) => false,
                    (true, false) => true,
                    (false, false) => self.bytes_lt(&(other as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_le(self, other: $int) -> bool {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_le(&(other as $big).to_be_bytes()),
                    (false, true) => true,
                    (true, false) => false,
                    (false, false) => self.bytes_ge(&(other as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_ge(self, other: $int) -> bool {
                match (self.sign_positive, other >= 0) {
                    (true, true) => self.bytes_ge(&(other as $big).to_be_bytes()),
                    (false, true) => false,
                    (true, false) => true,
                    (false, false) => self.bytes_le(&(other as $big).wrapping_neg().to_be_bytes()),
                }
            }
        }

        impl NumCmp<BigInt<'_>> for $int {
            #[cfg(test)]
            fn num_cmp_strategy(self, _other: BigInt<'_>) -> &'static str {
                "strategy, int vs BigInt"
            }

            #[inline]
            fn num_cmp(self, other: BigInt<'_>) -> Ordering {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_cmp(&(self as $big).to_be_bytes()).reverse(),
                    (false, true) => Ordering::Greater,
                    (true, false) => Ordering::Less,
                    (false, false) => other.bytes_cmp(&(self as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_eq(self, other: BigInt<'_>) -> bool {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_eq(&(self as $big).to_be_bytes()),
                    (false, false) => other.bytes_eq(&(self as $big).wrapping_neg().to_be_bytes()),
                    _ => false,
                }
            }

            #[inline]
            fn num_ne(self, other: BigInt<'_>) -> bool {
                !self.num_eq(other)
            }

            #[inline]
            fn num_lt(self, other: BigInt<'_>) -> bool {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_gt(&(self as $big).to_be_bytes()),
                    (false, true) => false,
                    (true, false) => true,
                    (false, false) => other.bytes_lt(&(self as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_gt(self, other: BigInt<'_>) -> bool {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_lt(&(self as $big).to_be_bytes()),
                    (false, true) => true,
                    (true, false) => false,
                    (false, false) => other.bytes_gt(&(self as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_le(self, other: BigInt<'_>) -> bool {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_ge(&(self as $big).to_be_bytes()),
                    (false, true) => false,
                    (true, false) => true,
                    (false, false) => other.bytes_le(&(self as $big).wrapping_neg().to_be_bytes()),
                }
            }

            #[inline]
            fn num_ge(self, other: BigInt<'_>) -> bool {
                match (other.sign_positive, self >= 0) {
                    (true, true) => other.bytes_le(&(self as $big).to_be_bytes()),
                    (false, true) => true,
                    (true, false) => false,
                    (false, false) => other.bytes_ge(&(self as $big).wrapping_neg().to_be_bytes()),
                }
            }
        }
    )*);
}

impl_for_uint_types_with_biguint! {
    u8; u16; u32; usize; u64; u128;
}

impl_for_int_types_with_biguint! {
    i8, u8; i16, u16; i32, u32; isize, usize; i64, u64; i128, u128;
}

impl_for_uint_types_with_bigint! {
    u8; u16; u32; usize; u64; u128;
}

impl_for_int_types_with_bigint! {
    i8, u8; i16, u16; i32, u32; isize, usize; i64, u64; i128, u128;
}
