use crate::{NumCmp, U128_BOUND_IN_F64};
use derive_deref_rs::Deref;
use malachite::natural::conversion::to_limbs::LimbIterator;
use malachite::{platform::Limb, Natural};
use malachite_base::num::logic::traits::SignificantBits;
use std::cmp::Ordering;
use std::iter::{Copied, FusedIterator, Rev};
use std::slice::Iter;

/// 高位优先的零分配字节迭代器；存储类型在创建时分派。
#[derive(Clone)]
pub enum BytesBe<'a> {
    Be(Copied<Iter<'a, u8>>),
    Le(Rev<Copied<Iter<'a, u8>>>),
    Natural(NaturalBytes<'a>),
}

/// Natural 的字节游标；两端分别缓存 Limb，支持交错读取而不重复构建 limbs。
#[derive(Clone)]
pub struct NaturalBytes<'a> {
    limbs: LimbIterator<'a>,
    front: usize,
    back: usize,
    high: (usize, Limb),
    low: (usize, Limb),
}
impl NaturalBytes<'_> {
    fn read(&mut self, index: usize, high: bool) -> u8 {
        let width = std::mem::size_of::<Limb>();
        let limb_index = index / width;
        let cache = if high { &mut self.high } else { &mut self.low };
        if cache.0 != limb_index {
            *cache = (limb_index, self.limbs[limb_index]);
        }
        (cache.1 >> ((index % width) * 8)) as u8
    }
}
impl Iterator for NaturalBytes<'_> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.front == self.back {
            return None;
        }
        self.back -= 1;
        Some(self.read(self.back, true))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.back - self.front;
        (len, Some(len))
    }
}
impl DoubleEndedIterator for NaturalBytes<'_> {
    fn next_back(&mut self) -> Option<u8> {
        if self.front == self.back {
            return None;
        }
        let index = self.front;
        self.front += 1;
        Some(self.read(index, false))
    }
}
impl ExactSizeIterator for NaturalBytes<'_> {}
impl FusedIterator for NaturalBytes<'_> {}

// 在热点循环外展开具体迭代器，循环内不再区分字节序或存储类型。
macro_rules! with_bytes {
    ($bytes:expr, $iter:ident => $body:expr) => {
        match $bytes {
            BytesBe::Be($iter) => $body,
            BytesBe::Le($iter) => $body,
            BytesBe::Natural($iter) => $body,
        }
    };
}
impl Iterator for BytesBe<'_> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        with_bytes!(self, iter => iter.next())
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        with_bytes!(self, iter => iter.size_hint())
    }
}
impl DoubleEndedIterator for BytesBe<'_> {
    fn next_back(&mut self) -> Option<u8> {
        with_bytes!(self, iter => iter.next_back())
    }
}
impl ExactSizeIterator for BytesBe<'_> {}
impl FusedIterator for BytesBe<'_> {}

const BYTES_BOUND_IN_F32: usize = f32::MAX_EXP as usize / u8::BITS as usize;
const BYTES_BOUND_IN_F64: usize = f64::MAX_EXP as usize / u8::BITS as usize;
const U64_BYTES: usize = (u64::BITS / u8::BITS) as usize;
const U64_MANTISSA_BYTES: usize = 53 / u8::BITS as usize + 1;
const U128_BYTES: usize = (u128::BITS / u8::BITS) as usize;

/// 零拷贝的无符号整数视图，大小端字节和 Natural 按数值统一比较。
/// 构造时裁掉高位零；私有存储确保调用方不能绕过规范化，视图保持 Copy。
///
/// ```rust
/// use malachite::Natural;
/// use pi_num_cmp::{bigint::BigUint, NumCmp};
/// let natural = Natural::from(256u32);
/// let a = BigUint::from_natural(&natural);
/// let b = BigUint::from_le_bytes(&[0, 1, 0]);
/// assert_eq!(a, b);
/// assert!(a.num_eq(256u32));
/// assert_eq!(a.bytes_be().collect::<Vec<_>>(), vec![1, 0]);
/// ```
///
/// 存储字段不公开，不能绕过构造函数的规范化约束：
/// ```compile_fail
/// use pi_num_cmp::bigint::BigUint;
/// let value = BigUint::BeBytes(&[0, 1]);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct BigUint<'a> {
    storage: BigUintStorage<'a>,
}

#[derive(Debug, Clone, Copy)]
enum BigUintStorage<'a> {
    /// 大端字节，高位在前。
    BeBytes(&'a [u8]),
    /// 小端字节，低位在前。
    LeBytes(&'a [u8]),
    /// 借用 malachite 幅值，通过 limbs 读取而不复制。
    Natural(&'a Natural),
}
impl<'a> From<&'a [u8]> for BigUint<'a> {
    #[inline]
    fn from(value: &'a [u8]) -> Self {
        BigUint::new(value)
    }
}
impl<'a> BigUint<'a> {
    #[inline]
    /// 借用大端字节；保留原构造入口的字节序含义。
    pub const fn new(value: &'a [u8]) -> Self {
        let start = Self::leading_zeros(value);
        let (_, data) = value.split_at(start);
        Self {
            storage: BigUintStorage::BeBytes(data),
        }
    }
    /// 借用小端字节，不复制底层数据。
    pub const fn from_le_bytes(value: &'a [u8]) -> Self {
        let mut end = value.len();
        while end > 0 && value[end - 1] == 0 {
            end -= 1;
        }
        let (data, _) = value.split_at(end);
        Self {
            storage: BigUintStorage::LeBytes(data),
        }
    }
    /// 直接借用 Natural，不创建临时字节缓冲。
    pub const fn from_natural(value: &'a Natural) -> Self {
        Self {
            storage: BigUintStorage::Natural(value),
        }
    }
    /// 若底层为大端字节，返回规范化后的原始借用切片。
    pub const fn as_be_bytes(&self) -> Option<&'a [u8]> {
        match self.storage {
            BigUintStorage::BeBytes(data) => Some(data),
            _ => None,
        }
    }
    /// 若底层为 Natural，返回原始借用，不复制数据。
    pub const fn as_natural(&self) -> Option<&'a Natural> {
        match self.storage {
            BigUintStorage::Natural(value) => Some(value),
            _ => None,
        }
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
    /// 有效字节数，不包含高位零。
    #[inline]
    pub fn len(&self) -> usize {
        match self.storage {
            BigUintStorage::BeBytes(data) | BigUintStorage::LeBytes(data) => data.len(),
            BigUintStorage::Natural(value) => value.significant_bits().div_ceil(8) as usize,
        }
    }
    /// 数值是否为零。
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// 从最高有效字节到最低有效字节迭代，不分配内存。
    /// 与原 as_slice 不同，支持没有连续大端切片的存储形式。
    pub fn bytes_be(self) -> BytesBe<'a> {
        match self.storage {
            BigUintStorage::BeBytes(data) => BytesBe::Be(data.iter().copied()),
            BigUintStorage::LeBytes(data) => BytesBe::Le(data.iter().copied().rev()),
            BigUintStorage::Natural(value) => BytesBe::Natural(NaturalBytes {
                limbs: value.limbs(),
                front: 0,
                back: value.significant_bits().div_ceil(8) as usize,
                high: (usize::MAX, 0),
                low: (usize::MAX, 0),
            }),
        }
    }
    #[inline]
    pub fn bits(&self) -> usize {
        self.len() << 3
    }
    #[inline]
    pub fn high_bits(&self) -> usize {
        self.bytes_be()
            .next()
            .map_or(0, |first| self.bits() - first.leading_zeros() as usize)
    }
    #[inline]
    fn to_u64(&self) -> u64 {
        let mut data = [0; U64_BYTES];
        with_bytes!(self.bytes_be(), iter => {
            for (out, byte) in data.iter_mut().zip(iter) { *out = byte; }
        });
        u64::from_be_bytes(data)
    }
    #[inline]
    fn to_u128(&self) -> u128 {
        let mut data = [0; U128_BYTES];
        let offset = U128_BYTES.saturating_sub(self.len());
        with_bytes!(self.bytes_be(), iter => {
            for (out, byte) in data[offset..].iter_mut().zip(iter) { *out = byte; }
        });
        u128::from_be_bytes(data)
    }
    fn finite_positive_f32_cmp(&self, other: f32) -> Ordering {
        if self.is_empty() {
            return if other == 0.0 {
                Ordering::Equal
            } else {
                Ordering::Less
            };
        } else if self.len() > BYTES_BOUND_IN_F32 {
            return Ordering::Greater;
        }
        let int = other.trunc();
        (self.to_u128(), int)
            .partial_cmp(&(int as u128, other))
            .unwrap()
    }
    fn finite_positive_f64_cmp(&self, other: f64) -> Ordering {
        if self.is_empty() {
            return if other == 0.0 {
                Ordering::Equal
            } else {
                Ordering::Less
            };
        } else if self.len() <= U128_BYTES {
            if other >= U128_BOUND_IN_F64 {
                return Ordering::Less;
            }
            let int = other.trunc();
            return (self.to_u128(), int)
                .partial_cmp(&(int as u128, other))
                .unwrap();
        } else if self.len() > BYTES_BOUND_IN_F64 {
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
            if with_bytes!(self.bytes_be(), iter => iter.skip(U64_BYTES).any(|d| d != 0)) {
                return Ordering::Greater;
            }
            Ordering::Equal
        } else {
            // 情况2: 指数偏移 < 0 (f 表示为分数), 分子为 significand, 分母为 2^(-exp_power)
            // 必定小于 2^53
            if self.len() > U64_MANTISSA_BYTES {
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
        let len = self.len();
        if len > N {
            return Ordering::Greater;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return len.cmp(&other.len());
        }
        with_bytes!(self.bytes_be(), left => left.cmp(other.iter().copied()))
    }
    #[inline]
    fn bytes_eq<const N: usize>(self, other: &[u8; N]) -> bool {
        let len = self.len();
        if len > N {
            return false;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return false;
        }
        with_bytes!(self.bytes_be(), left => left.eq(other.iter().copied()))
    }

    #[inline]
    fn bytes_ne<const N: usize>(self, other: &[u8; N]) -> bool {
        !self.bytes_eq(other)
    }

    #[inline]
    fn bytes_lt<const N: usize>(self, other: &[u8; N]) -> bool {
        let len = self.len();
        if len > N {
            return false;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return len < other.len();
        }
        with_bytes!(self.bytes_be(), left => left.lt(other.iter().copied()))
    }

    #[inline]
    fn bytes_gt<const N: usize>(self, other: &[u8; N]) -> bool {
        let len = self.len();
        if len > N {
            return true;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return len > other.len();
        }
        with_bytes!(self.bytes_be(), left => left.gt(other.iter().copied()))
    }

    #[inline]
    fn bytes_le<const N: usize>(self, other: &[u8; N]) -> bool {
        let len = self.len();
        if len > N {
            return false;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return len < other.len();
        }
        with_bytes!(self.bytes_be(), left => left.le(other.iter().copied()))
    }

    #[inline]
    fn bytes_ge<const N: usize>(self, other: &[u8; N]) -> bool {
        let len = self.len();
        if len > N {
            return true;
        }
        // 同宽时直接比较；只有不足 N 字节时才扫描对方的高位零。
        let other = if len < N {
            &other[Self::leading_zeros(other)..]
        } else {
            &other[..]
        };
        if len != other.len() {
            return len > other.len();
        }
        with_bytes!(self.bytes_be(), left => left.ge(other.iter().copied()))
    }
}
impl<'a> Ord for BigUint<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.len()
            .cmp(&other.len())
            .then_with(|| with_bytes!(self.bytes_be(), left => with_bytes!(other.bytes_be(), right => left.cmp(right))))
    }
}
impl PartialEq for BigUint<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for BigUint<'_> {}
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
        self.num_cmp(other).is_le()
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
    pub fn new(biguint: BigUint<'a>, sign_positive: bool) -> Self {
        BigInt {
            biguint,
            sign_positive: sign_positive || biguint.is_empty(),
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
        self.sign_positive = sign_positive || self.biguint.is_empty();
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
        match (self.sign_positive, other >= 0.0) {
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
