use crate::bigint::{BigInt, BigUint};
use crate::NumCmp;
use malachite::{platform::Limb, Integer as BigInteger, Natural};
use malachite_base::num::basic::traits::Zero;
use malachite_base::num::conversion::traits::RoundingFrom;
use malachite_base::num::logic::traits::SignificantBits;
use malachite_base::rounding_modes::RoundingMode;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Mul, Sub};

/// 拥有数据的通用数值，适合数据库记录和内存集合。
///
/// 相等、排序和哈希按数值而非变体判断：整数 1 与浮点数 1.0 相等，
/// 正负零相等，所有 NaN 相等且排在正无穷之后。跨类型比较复用本库的
/// [`NumCmp`]；两个大整数直接使用 malachite 的比较。
///
/// 整数运算按需从 I64 提升到 I128，再提升到 Integer；参与运算的
/// Integer 不会自动缩回原生类型。浮点混算返回 F64，可能损失精度。
/// 四则运算消耗操作数，并返回 Result；除以任何类型的零均报错。
///
/// serde 和 fory 支持分别由同名 feature 启用，序列化保留变体。
/// 不承诺序列化格式或哈希值跨版本稳定。
///
/// ```rust
/// use pi_num_cmp::{Number, NumberError};
/// assert_eq!(Number::I64(1), Number::F64(1.0));
/// assert_eq!((Number::I64(7) / Number::I64(2))?, Number::I64(3));
/// # Ok::<(), NumberError>(())
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Number {
    /// 64 位有符号整数，常用整数的快速路径。
    I64(i64),
    /// 128 位有符号整数，避免较大整数立即分配堆内存。
    I128(i128),
    /// IEEE 754 双精度浮点数，支持 NaN 和正负无穷。
    F64(f64),
    /// malachite 任意精度有符号整数，持有底层存储。
    Integer(BigInteger),
}

/// 数值运算中可恢复的错误；整数溢出通过提升类型处理。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberError {
    /// 除数为整数零、浮点正零或浮点负零。
    DivisionByZero,
}

// 仅展开枚举并适配借用视图，跨类型比较交给 NumCmp，不重复实现比较算法。
macro_rules! with_number {
    ($number:expr, $value:ident => $body:expr) => {
        match $number {
            Number::I64($value) => {
                let $value = *$value;
                $body
            }
            Number::I128($value) => {
                let $value = *$value;
                $body
            }
            Number::F64($value) => {
                let $value = *$value;
                $body
            }
            Number::Integer($value) => {
                if let Ok(small) = i128::try_from($value) {
                    let $value = small;
                    $body
                } else {
                    // 直接借用 Natural 幅值，不创建中间字节缓冲。
                    let $value = BigInt::new(
                        BigUint::from_natural($value.unsigned_abs_ref()),
                        $value >= &BigInteger::ZERO,
                    );
                    $body
                }
            }
        }
    };
}

impl Number {
    fn cmp_value(&self, other: &Self) -> Ordering {
        if let (Self::Integer(a), Self::Integer(b)) = (self, other) {
            return a.cmp(b);
        }
        with_number!(self, left => with_number!(other, right => left.num_cmp(right)))
    }

    fn as_f64(&self) -> f64 {
        match self {
            Self::I64(v) => *v as f64,
            Self::I128(v) => *v as f64,
            Self::F64(v) => *v,
            Self::Integer(v) => {
                let rounded = f64::rounding_from(v, RoundingMode::Nearest).0;
                if rounded.abs() == f64::MAX && v.unsigned_abs_ref().significant_bits() >= 1024 {
                    // malachite 的 Nearest 饱和到最大有限值；这里恢复 IEEE 最近偶数舍入的溢出阈值。
                    let threshold =
                        (Natural::from(1u8) << 1024usize) - (Natural::from(1u8) << 970usize);
                    if v.unsigned_abs_ref() >= &threshold {
                        return if v < &BigInteger::ZERO {
                            f64::NEG_INFINITY
                        } else {
                            f64::INFINITY
                        };
                    }
                }
                rounded
            }
        }
    }

    fn operate(self, rhs: Self, op: Operation) -> Result<Self, NumberError> {
        if op == Operation::Div
            && match &rhs {
                Self::I64(v) => *v == 0,
                Self::I128(v) => *v == 0,
                Self::F64(v) => *v == 0.0,
                Self::Integer(v) => v == &BigInteger::ZERO,
            }
        {
            return Err(NumberError::DivisionByZero);
        }
        if matches!(self, Self::F64(_)) || matches!(rhs, Self::F64(_)) {
            let (a, b) = (self.as_f64(), rhs.as_f64());
            return Ok(Self::F64(match op {
                Operation::Add => a + b,
                Operation::Sub => a - b,
                Operation::Mul => a * b,
                Operation::Div => a / b,
            }));
        }
        match (self, rhs) {
            (Self::I64(a), Self::I64(b)) => {
                let result = match op {
                    Operation::Add => a.checked_add(b),
                    Operation::Sub => a.checked_sub(b),
                    Operation::Mul => a.checked_mul(b),
                    Operation::Div => a.checked_div(b),
                };
                if let Some(value) = result {
                    return Ok(Self::I64(value));
                }
                let (a, b) = (a as i128, b as i128);
                let result = match op {
                    Operation::Add => a.checked_add(b),
                    Operation::Sub => a.checked_sub(b),
                    Operation::Mul => a.checked_mul(b),
                    Operation::Div => a.checked_div(b),
                };
                if let Some(value) = result {
                    return Ok(Self::I128(value));
                }
                Ok(Self::Integer(Self::big_operation(
                    BigInteger::from(a),
                    BigInteger::from(b),
                    op,
                )))
            }
            (Self::I128(a), Self::I128(b)) => Ok(Self::checked_native(a, b, op)),
            (Self::I64(a), Self::I128(b)) => Ok(Self::checked_native(a as i128, b, op)),
            (Self::I128(a), Self::I64(b)) => Ok(Self::checked_native(a, b as i128, op)),
            (Self::Integer(a), Self::I64(b)) => Ok(Self::Integer(Self::big_operation(
                a,
                BigInteger::from(b),
                op,
            ))),
            (Self::Integer(a), Self::I128(b)) => Ok(Self::Integer(Self::big_operation(
                a,
                BigInteger::from(b),
                op,
            ))),
            (Self::Integer(a), Self::Integer(b)) => {
                Ok(Self::Integer(Self::big_operation(a, b, op)))
            }
            (Self::I64(a), Self::Integer(b)) => Ok(Self::Integer(Self::big_operation(
                BigInteger::from(a),
                b,
                op,
            ))),
            (Self::I128(a), Self::Integer(b)) => Ok(Self::Integer(Self::big_operation(
                BigInteger::from(a),
                b,
                op,
            ))),
            _ => unreachable!(),
        }
    }

    fn checked_native(a: i128, b: i128, op: Operation) -> Self {
        let result = match op {
            Operation::Add => a.checked_add(b),
            Operation::Sub => a.checked_sub(b),
            Operation::Mul => a.checked_mul(b),
            Operation::Div => a.checked_div(b),
        };
        result.map(Self::I128).unwrap_or_else(|| {
            Self::Integer(Self::big_operation(
                BigInteger::from(a),
                BigInteger::from(b),
                op,
            ))
        })
    }

    fn big_operation(a: BigInteger, b: BigInteger, op: Operation) -> BigInteger {
        // 移交所有权，允许 malachite 复用操作数的底层缓冲；不克隆已有大整数。
        match op {
            Operation::Add => a + b,
            Operation::Sub => a - b,
            Operation::Mul => a * b,
            Operation::Div => a / b,
        }
    }

    /// 相加；整数溢出时提升类型，浮点混算按 f64 舍入。
    pub fn checked_add(self, rhs: Self) -> Result<Self, NumberError> {
        self.operate(rhs, Operation::Add)
    }
    /// 相减；整数溢出时提升类型，保留减法的操作数顺序。
    pub fn checked_sub(self, rhs: Self) -> Result<Self, NumberError> {
        self.operate(rhs, Operation::Sub)
    }
    /// 相乘；整数结果精确，浮点结果允许产生无穷或 NaN。
    pub fn checked_mul(self, rhs: Self) -> Result<Self, NumberError> {
        self.operate(rhs, Operation::Mul)
    }
    /// 相除；纯整数除法向零截断，浮点混算返回 F64。
    ///
    /// # 错误
    /// 任意类型的零除数均返回 [NumberError::DivisionByZero]，包括浮点负零。
    pub fn checked_div(self, rhs: Self) -> Result<Self, NumberError> {
        self.operate(rhs, Operation::Div)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
}

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
        self.cmp_value(other).is_eq()
    }
}
impl Eq for Number {}
impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp_value(other))
    }
}
impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_value(other)
    }
}

impl Hash for Number {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Self::F64(f) = self {
            if f.is_nan() {
                2u8.hash(state);
                return;
            }
            if f.is_infinite() {
                1u8.hash(state);
                f.is_sign_negative().hash(state);
                return;
            }
        }
        match self {
            Self::I64(v) => hash_integer(v.unsigned_abs() as u128, *v < 0, state),
            Self::I128(v) => hash_integer(v.unsigned_abs(), *v < 0, state),
            Self::Integer(v) => {
                let magnitude = v.unsigned_abs_ref();
                hash_digits(
                    magnitude.limbs().flat_map(|limb| {
                        [limb as u32, ((limb as u64) >> 32) as u32]
                            .into_iter()
                            .take(std::mem::size_of::<Limb>() / 4)
                    }),
                    magnitude.significant_bits(),
                    magnitude.trailing_zeros().unwrap_or(0),
                    v < &BigInteger::ZERO,
                    0,
                    state,
                );
            }
            Self::F64(v) => {
                let bits = v.to_bits();
                let exp = ((bits >> 52) & 0x7ff) as i32;
                let fraction = bits & ((1u64 << 52) - 1);
                let mantissa = if exp == 0 {
                    fraction
                } else {
                    fraction | (1u64 << 52)
                };
                let power = if exp == 0 { -1074 } else { exp - 1075 };
                hash_digits(
                    [mantissa as u32, (mantissa >> 32) as u32].into_iter(),
                    64 - mantissa.leading_zeros() as u64,
                    mantissa.trailing_zeros() as u64,
                    v.is_sign_negative(),
                    power,
                    state,
                );
            }
        }
    }
}

fn hash_integer<H: Hasher>(magnitude: u128, negative: bool, state: &mut H) {
    hash_digits(
        (0..4).map(|i| (magnitude >> (i * 32)) as u32),
        128 - magnitude.leading_zeros() as u64,
        magnitude.trailing_zeros() as u64,
        negative,
        0,
        state,
    );
}

// 统一哈希为“符号 + 二进制指数 + 去除低位零后的幅值”，保证跨变体相等则哈希相同。
// digits 按低位在前迭代；大整数借用 limbs，不构造临时 Integer 或复制幅值。
fn hash_digits<H: Hasher>(
    digits: impl Iterator<Item = u32>,
    bits: u64,
    trailing: u64,
    negative: bool,
    power: i32,
    state: &mut H,
) {
    0u8.hash(state);
    if bits == 0 {
        false.hash(state);
        0i32.hash(state);
        0u64.hash(state);
        return;
    }
    negative.hash(state);
    (power + trailing as i32).hash(state);
    let count = (bits - trailing).div_ceil(32);
    count.hash(state);
    let offset = (trailing % 32) as u32;
    let mut digits = digits.skip((trailing / 32) as usize).peekable();
    for _ in 0..count {
        let current = digits.next().unwrap_or(0);
        let normalized = if offset == 0 {
            current
        } else {
            (current >> offset) | (digits.peek().copied().unwrap_or(0) << (32 - offset))
        };
        normalized.hash(state);
    }
}

impl Add for Number {
    type Output = Result<Self, NumberError>;
    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
    }
}
impl Sub for Number {
    type Output = Result<Self, NumberError>;
    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
    }
}
impl Mul for Number {
    type Output = Result<Self, NumberError>;
    fn mul(self, rhs: Self) -> Self::Output {
        self.checked_mul(rhs)
    }
}
impl Div for Number {
    type Output = Result<Self, NumberError>;
    fn div(self, rhs: Self) -> Self::Output {
        self.checked_div(rhs)
    }
}

#[cfg(feature = "fory")]
/// Fory 自定义序列化；先注册 register_serializer::<Number>，再使用 *_with 接口。
/// 负载以变体标签区分；大整数保存符号与大端幅值，不保存 malachite 内存布局。
impl fory::Serializer for Number {
    type Target = Self;

    fn write_data(value: &Self, context: &mut fory::WriteContext<'_>) -> Result<(), fory::Error> {
        match value {
            Self::I64(v) => {
                context.writer.write_u8(0);
                context.writer.write_i64(*v);
            }
            Self::I128(v) => {
                context.writer.write_u8(1);
                context.writer.write_bytes(&v.to_be_bytes());
            }
            Self::F64(v) => {
                context.writer.write_u8(2);
                context.writer.write_f64(*v);
            }
            Self::Integer(v) => {
                context.writer.write_u8(3);
                context
                    .writer
                    .write_u8(if v < &BigInteger::ZERO { 1 } else { 0 });
                let magnitude = v.unsigned_abs_ref();
                let mut bytes =
                    Vec::with_capacity(magnitude.limbs().len() * std::mem::size_of::<Limb>());
                for limb in magnitude.limbs().rev() {
                    bytes.extend_from_slice(&limb.to_be_bytes());
                }
                context.writer.write_var_u32(bytes.len() as u32);
                context.writer.write_bytes(&bytes);
            }
        }
        Ok(())
    }

    fn read_data(context: &mut fory::ReadContext<'_>) -> Result<Self, fory::Error> {
        match context.reader.read_u8()? {
            0 => Ok(Self::I64(context.reader.read_i64()?)),
            1 => {
                let bytes: [u8; 16] = context.reader.read_bytes(16)?.try_into().unwrap();
                Ok(Self::I128(i128::from_be_bytes(bytes)))
            }
            2 => Ok(Self::F64(context.reader.read_f64()?)),
            3 => {
                let negative = context.reader.read_u8()? != 0;
                let len = context.reader.read_var_u32()? as usize;
                let bytes = context.reader.read_bytes(len)?;
                let limb_bytes = std::mem::size_of::<Limb>();
                let mut limbs = Vec::with_capacity(len.div_ceil(limb_bytes));
                for chunk in bytes.rchunks(limb_bytes) {
                    let mut limb = 0;
                    for byte in chunk {
                        limb = (limb << 8) | (*byte as Limb);
                    }
                    limbs.push(limb);
                }
                let magnitude = Natural::from_owned_limbs_asc(limbs);
                Ok(Self::Integer(BigInteger::from_sign_and_abs(
                    !negative, magnitude,
                )))
            }
            _ => Err(fory::Error::invalid_data("invalid Number variant")),
        }
    }

    fn default_value(_: &mut fory::ReadContext<'_>) -> Result<Self, fory::Error> {
        Ok(Self::I64(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn hash(value: &Number) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn comparison_and_hash() {
        let one = [
            Number::I64(1),
            Number::I128(1),
            Number::F64(1.0),
            Number::Integer(BigInteger::from(1)),
        ];
        for a in &one {
            for b in &one {
                assert_eq!(a, b);
                assert_eq!(hash(a), hash(b));
            }
        }
        assert_eq!(Number::Integer(BigInteger::from(0)), Number::F64(-0.0));
        assert_eq!(
            hash(&Number::Integer(BigInteger::from(0))),
            hash(&Number::F64(-0.0))
        );
        assert!(Number::F64(f64::NAN) > Number::Integer(BigInteger::from(1)));
        assert_eq!(
            Number::I128(i128::MAX).cmp(&Number::F64(2f64.powi(127))),
            i128::MAX.num_cmp(2f64.powi(127))
        );
        assert_eq!(
            Number::Integer(BigInteger::from(1)).cmp(&Number::F64(1.0)),
            BigInt::new(BigUint::new(&[1]), true).num_cmp(1.0f64)
        );
        let values = [
            Number::I64(-256),
            Number::I128(-256),
            Number::Integer(BigInteger::from(-256)),
            Number::F64(-256.0),
            Number::I64(0),
            Number::F64(-0.0),
            Number::I128(1 << 80),
            Number::F64((1u128 << 80) as f64),
            Number::Integer(BigInteger::from(1u128 << 80)),
            Number::F64(0.5),
            Number::F64(f64::from_bits(1)),
        ];
        for a in &values {
            for b in &values {
                if a == b {
                    assert_eq!(hash(a), hash(b), "{a:?} vs {b:?}");
                }
            }
        }
        let exact = BigInteger::from(1u8) << 256usize;
        assert_eq!(
            hash(&Number::Integer(exact)),
            hash(&Number::F64(2f64.powi(256)))
        );
        assert_eq!(
            Number::Integer(BigInteger::from(1u8) << 256usize),
            Number::F64(2f64.powi(256))
        );
        assert!(
            Number::Integer((BigInteger::from(1u8) << 256usize) + BigInteger::from(1u8))
                > Number::F64(2f64.powi(256))
        );
        let odd: BigInteger = (BigInteger::from(1u8) << 256usize) + BigInteger::from(1u8);
        assert_ne!(
            hash(&Number::Integer(odd)),
            hash(&Number::F64(2f64.powi(256)))
        );
        let huge: BigInteger = BigInteger::from(1u8) << 256usize;
        let sorted = [
            Number::Integer(-huge.clone()),
            Number::I128(i128::MIN),
            Number::I64(-1),
            Number::F64(-0.5),
            Number::I64(0),
            Number::F64(0.5),
            Number::I128(i128::MAX),
            Number::Integer(huge),
            Number::F64(f64::INFINITY),
            Number::F64(f64::NAN),
        ];
        for (i, a) in sorted.iter().enumerate() {
            for (j, b) in sorted.iter().enumerate() {
                assert_eq!(a.cmp(b), i.cmp(&j), "{a:?} vs {b:?}");
            }
        }
    }

    #[test]
    fn arithmetic_promotes_only_when_needed() {
        assert!(matches!(
            (Number::I64(1) + Number::I64(2)).unwrap(),
            Number::I64(3)
        ));
        assert!(
            matches!((Number::I64(i64::MAX) + Number::I64(1)).unwrap(), Number::I128(v) if v == i64::MAX as i128 + 1)
        );
        assert!(
            matches!((Number::I128(i128::MAX) + Number::I64(1)).unwrap(), Number::Integer(v) if v == BigInteger::from(i128::MAX) + BigInteger::from(1))
        );
        assert!(matches!(
            (Number::I64(3) / Number::I64(2)).unwrap(),
            Number::I64(1)
        ));
        assert_eq!(
            Number::I64(1).checked_div(Number::F64(-0.0)),
            Err(NumberError::DivisionByZero)
        );
        assert!(matches!(
            (Number::I64(1) + Number::F64(0.5)).unwrap(),
            Number::F64(1.5)
        ));
        let beyond_f64: BigInteger = BigInteger::from(1u8) << 1024usize;
        assert!(
            matches!((Number::Integer(beyond_f64) + Number::F64(0.0)).unwrap(), Number::F64(v) if v == f64::INFINITY)
        );
        assert!(
            matches!((Number::Integer(BigInteger::from(1u128 << 100)) + Number::I64(1)).unwrap(), Number::Integer(v) if v == BigInteger::from(1u128 << 100) + BigInteger::from(1))
        );
        assert!(
            matches!((Number::Integer(BigInteger::from(1u128 << 127)) + Number::I64(1)).unwrap(), Number::Integer(v) if v == BigInteger::from(1u128 << 127) + BigInteger::from(1))
        );
        assert!(
            matches!((Number::I64(1) - Number::Integer(BigInteger::from(3))).unwrap(), Number::Integer(v) if v == BigInteger::from(-2))
        );
        assert!(matches!(
            (Number::I128(5) / Number::I64(2)).unwrap(),
            Number::I128(2)
        ));
        assert!(
            matches!((Number::Integer(BigInteger::from(-7)) / Number::I64(2)).unwrap(), Number::Integer(v) if v == BigInteger::from(-3))
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serde_roundtrip() {
        for value in [
            Number::I64(1),
            Number::I128(i128::MAX),
            Number::F64(1.5),
            Number::Integer((BigInteger::from(i128::MAX) + BigInteger::from(1)) << 4usize),
            Number::Integer(-((BigInteger::from(i128::MAX) + BigInteger::from(1)) << 4usize)),
        ] {
            let encoded = serde_json::to_string(&value).unwrap();
            let decoded: Number = serde_json::from_str(&encoded).unwrap();
            assert_eq!(
                std::mem::discriminant(&value),
                std::mem::discriminant(&decoded)
            );
            assert_eq!(value, decoded);
        }
    }

    #[cfg(feature = "fory")]
    #[test]
    fn fory_roundtrip() {
        let mut fory = fory::Fory::builder().xlang(false).build();
        fory.register_serializer::<Number>(100).unwrap();
        for value in [
            Number::I64(1),
            Number::I128(i128::MAX),
            Number::F64(1.5),
            Number::Integer((BigInteger::from(i128::MAX) + BigInteger::from(1)) << 4usize),
            Number::Integer(-((BigInteger::from(i128::MAX) + BigInteger::from(1)) << 4usize)),
        ] {
            let encoded = fory.serialize_with::<Number>(&value).unwrap();
            let decoded: Number = fory.deserialize_with::<Number>(&encoded).unwrap();
            assert_eq!(
                std::mem::discriminant(&value),
                std::mem::discriminant(&decoded)
            );
            assert_eq!(value, decoded);
        }
    }
}
