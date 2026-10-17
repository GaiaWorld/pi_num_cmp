use crate::{
    bigint::{BigInt, BigUint},
    NumCmp, Number,
};
use malachite::Integer;
use malachite_base::num::basic::traits::Zero;
use std::cmp::Ordering;

/// 数值的借用视图；原生数值保存在栈上，大整数借用 Natural 或序列化字节。
/// 比较复用 NumCmp，NaN 相等且最大，正负零相等，不构造临时 Integer。
///
/// ```rust
/// use pi_num_cmp::{Number, NumberRef};
/// let value = Number::I128(42);
/// let view = value.as_number_ref();
/// assert_eq!(view, NumberRef::F64(42.0));
/// assert_eq!(view, value);
/// ```
#[derive(Debug, Clone, Copy)]
pub enum NumberRef<'a> {
    /// 栈上 64 位整数。
    I64(i64),
    /// 栈上 128 位整数。
    I128(i128),
    /// 栈上双精度浮点数。
    F64(f64),
    /// 借用原始大整数幅值和符号。
    Integer(BigInt<'a>),
}

macro_rules! dispatch {
    ($number:expr, $v:ident => $body:expr) => {
        match $number {
            NumberRef::I64($v) => $body,
            NumberRef::I128($v) => $body,
            NumberRef::F64($v) => $body,
            NumberRef::Integer($v) => $body,
        }
    };
}

impl<'a> From<&'a Number> for NumberRef<'a> {
    fn from(value: &'a Number) -> Self {
        match value {
            Number::I64(v) => Self::I64(*v),
            Number::I128(v) => Self::I128(*v),
            Number::F64(v) => Self::F64(*v),
            Number::Integer(v) => Self::Integer(BigInt::new(
                BigUint::from_natural(v.unsigned_abs_ref()),
                v >= &Integer::ZERO,
            )),
        }
    }
}

impl Number {
    /// 创建零拷贝数值视图；视图不能超过当前 Number 的生命周期。
    pub fn as_number_ref(&self) -> NumberRef<'_> {
        self.into()
    }
}

impl PartialEq for NumberRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for NumberRef<'_> {}
impl PartialOrd for NumberRef<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for NumberRef<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        dispatch!(*self, a => dispatch!(*other, b => a.num_cmp(b)))
    }
}
impl PartialEq<Number> for NumberRef<'_> {
    fn eq(&self, other: &Number) -> bool {
        *self == other.as_number_ref()
    }
}
impl PartialOrd<Number> for NumberRef<'_> {
    fn partial_cmp(&self, other: &Number) -> Option<Ordering> {
        Some(self.cmp(&other.as_number_ref()))
    }
}
impl PartialEq<NumberRef<'_>> for Number {
    fn eq(&self, other: &NumberRef<'_>) -> bool {
        self.as_number_ref() == *other
    }
}
impl PartialOrd<NumberRef<'_>> for Number {
    fn partial_cmp(&self, other: &NumberRef<'_>) -> Option<Ordering> {
        Some(self.as_number_ref().cmp(other))
    }
}
impl NumCmp<NumberRef<'_>> for NumberRef<'_> {
    #[cfg(test)]
    fn num_cmp_strategy(self, _: NumberRef<'_>) -> &'static str {
        "borrowed number"
    }
    fn num_cmp(self, other: NumberRef<'_>) -> Ordering {
        self.cmp(&other)
    }
    fn num_eq(self, other: NumberRef<'_>) -> bool {
        self == other
    }
    fn num_ne(self, other: NumberRef<'_>) -> bool {
        self != other
    }
    fn num_lt(self, other: NumberRef<'_>) -> bool {
        self < other
    }
    fn num_gt(self, other: NumberRef<'_>) -> bool {
        self > other
    }
    fn num_le(self, other: NumberRef<'_>) -> bool {
        self <= other
    }
    fn num_ge(self, other: NumberRef<'_>) -> bool {
        self >= other
    }
}

#[cfg(feature = "fory")]
impl<'a> NumberRef<'a> {
    /// 读取 Number 自定义 serializer 的负载，不含 Fory 外层协议。
    /// 返回视图及未消费的尾部；非法标签、符号或截断数据返回错误。
    pub fn read_fory_payload(input: &'a [u8]) -> Result<(Self, &'a [u8]), fory::Error> {
        let mut reader = fory::Reader::new(input);
        let value = match reader.read_u8()? {
            0 => Self::I64(reader.read_i64()?),
            1 => Self::I128(i128::from_be_bytes(
                reader.read_bytes(16)?.try_into().unwrap(),
            )),
            2 => Self::F64(reader.read_f64()?),
            3 => {
                let sign = reader.read_u8()?;
                if sign > 1 {
                    return Err(fory::Error::invalid_data("invalid Number sign"));
                }
                let len = reader.read_var_u32()? as usize;
                let start = reader.get_cursor();
                reader.skip(len)?;
                Self::Integer(BigInt::new(
                    BigUint::new(&input[start..reader.get_cursor()]),
                    sign == 0,
                ))
            }
            _ => return Err(fory::Error::invalid_data("invalid Number variant")),
        };
        Ok((value, &input[reader.get_cursor()..]))
    }

    /// 在专用读取端注册定位器，ID 必须与写入端 Number 的 ID 相同。
    /// 在首次读取前调用一次；不要在该实例上用相同 ID 注册 Number。
    pub fn register_fory(fory: &mut fory::Fory, type_id: u32) -> Result<(), fory::Error> {
        fory.register_serializer::<PayloadRange>(type_id)
    }

    /// 从完整 Fory 根消息读取借用视图，外层协议交给 Fory 校验。
    /// 需先调用 register_fory；同一读取实例可重复使用。
    /// 大整数不复制，Fory 外层协议处理本身可能分配内存。
    pub fn from_fory(fory: &fory::Fory, input: &'a [u8]) -> Result<Self, fory::Error> {
        let range = fory.deserialize_with::<PayloadRange>(input)?;
        let payload = input
            .get(range.start..range.end)
            .ok_or_else(|| fory::Error::invalid_data("invalid Number payload range"))?;
        let (value, rest) = Self::read_fory_payload(payload)?;
        if !rest.is_empty() {
            return Err(fory::Error::invalid_data("trailing Number payload bytes"));
        }
        Ok(value)
    }
}

#[cfg(feature = "fory")]
struct PayloadRange {
    start: usize,
    end: usize,
}

#[cfg(feature = "fory")]
impl fory::Serializer for PayloadRange {
    type Target = Self;
    fn write_data(_: &Self, _: &mut fory::WriteContext<'_>) -> Result<(), fory::Error> {
        Err(fory::Error::invalid_data("NumberRef locator is read-only"))
    }
    fn read_data(context: &mut fory::ReadContext<'_>) -> Result<Self, fory::Error> {
        let start = context.reader.get_cursor();
        match context.reader.read_u8()? {
            0 | 2 => context.reader.skip(8)?,
            1 => context.reader.skip(16)?,
            3 => {
                if context.reader.read_u8()? > 1 {
                    return Err(fory::Error::invalid_data("invalid Number sign"));
                }
                let len = context.reader.read_var_u32()? as usize;
                context.reader.skip(len)?;
            }
            _ => return Err(fory::Error::invalid_data("invalid Number variant")),
        }
        Ok(Self {
            start,
            end: context.reader.get_cursor(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn values() -> Vec<Number> {
        vec![
            Number::F64(f64::NEG_INFINITY),
            Number::Integer(-(Integer::from(1u8) << 256usize)),
            Number::I128(i128::MIN),
            Number::I64(-1),
            Number::F64(-0.5),
            Number::I64(0),
            Number::F64(-0.0),
            Number::Integer(Integer::ZERO),
            Number::I64(1),
            Number::I128(1),
            Number::F64(1.0),
            Number::Integer(Integer::from(1)),
            Number::I128(i128::MAX),
            Number::Integer(Integer::from(1u8) << 256usize),
            Number::F64(f64::MAX),
            Number::F64(f64::INFINITY),
            Number::F64(f64::NAN),
        ]
    }

    #[test]
    fn borrowed_comparison_matches_owned() {
        let values = values();
        for a in &values {
            let ar = a.as_number_ref();
            if let (Number::Integer(original), NumberRef::Integer(view)) = (a, ar) {
                let magnitude = view.as_natural().unwrap();
                assert!(std::ptr::eq(magnitude, original.unsigned_abs_ref()));
            }
            for b in &values {
                let br = b.as_number_ref();
                let expected = a.cmp(b);
                assert_eq!(ar.cmp(&br), expected);
                assert_eq!(ar.num_cmp(br), expected);
                assert_eq!(ar.num_eq(br), expected.is_eq());
                assert_eq!(ar.num_ne(br), expected.is_ne());
                assert_eq!(ar.num_lt(br), expected.is_lt());
                assert_eq!(ar.num_gt(br), expected.is_gt());
                assert_eq!(ar.num_le(br), expected.is_le());
                assert_eq!(ar.num_ge(br), expected.is_ge());
                assert_eq!(ar.partial_cmp(b), Some(expected));
                assert_eq!(a.partial_cmp(&br), Some(expected));
                assert_eq!(ar == *b, expected.is_eq());
                assert_eq!(*a == br, expected.is_eq());
            }
        }
    }

    #[cfg(feature = "fory")]
    #[test]
    fn full_fory_message_borrows_input() {
        let mut writer = fory::Fory::builder().xlang(false).build();
        writer.register_serializer::<Number>(100).unwrap();
        let mut reader = fory::Fory::builder().xlang(false).build();
        NumberRef::register_fory(&mut reader, 100).unwrap();
        for value in values() {
            let bytes = writer.serialize_with::<Number>(&value).unwrap();
            let view = NumberRef::from_fory(&reader, &bytes).unwrap();
            assert_eq!(view, value);
            if let NumberRef::Integer(view) = view {
                let magnitude = view.as_be_bytes().unwrap();
                let base = bytes.as_ptr() as usize;
                let ptr = magnitude.as_ptr() as usize;
                assert!(ptr >= base && ptr + magnitude.len() <= base + bytes.len());
            }
        }
    }

    #[cfg(feature = "fory")]
    #[test]
    fn payload_validation_and_remainder() {
        let payload = [3, 1, 3, 0, 1, 0, 99];
        let (view, rest) = NumberRef::read_fory_payload(&payload).unwrap();
        assert_eq!(view, Number::I64(-256));
        assert_eq!(rest, &[99]);
        let NumberRef::Integer(view) = view else {
            panic!("not an integer")
        };
        let bytes = view.as_be_bytes().unwrap();
        assert!(std::ptr::eq(bytes.as_ptr(), payload[4..].as_ptr()));
        for end in 0..6 {
            assert!(NumberRef::read_fory_payload(&payload[..end]).is_err());
        }
        for input in [
            &[4][..],
            &[3, 2, 0],
            &[3, 0, 128],
            &[3, 0, 255, 255, 255, 255, 15],
        ] {
            assert!(NumberRef::read_fory_payload(input).is_err());
        }
        let (zero, _) = NumberRef::read_fory_payload(&[3, 1, 0]).unwrap();
        assert_eq!(zero, Number::I64(0));
        let mut writer = fory::Fory::builder().xlang(false).build();
        writer.register_serializer::<Number>(100).unwrap();
        let message = writer
            .serialize_with::<Number>(&Number::Integer(Integer::from(1u8) << 256usize))
            .unwrap();
        for end in 0..message.len() {
            let mut reader = fory::Fory::builder().xlang(false).build();
            NumberRef::register_fory(&mut reader, 100).unwrap();
            assert!(NumberRef::from_fory(&reader, &message[..end]).is_err());
        }
        let mut wrong_id = fory::Fory::builder().xlang(false).build();
        NumberRef::register_fory(&mut wrong_id, 101).unwrap();
        assert!(NumberRef::from_fory(&wrong_id, &message).is_err());
    }
}
