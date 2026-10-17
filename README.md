

# pi_num_cmp

[![Crates.io](https://img.shields.io/crates/v/pi_num_cmp)](https://crates.io/crates/pi_num_cmp)
[![Documentation](https://docs.rs/pi_num_cmp/badge.svg)](https://docs.rs/pi_num_cmp)

`pi_num_cmp` 是一个 Rust 库，提供了跨类型数值比较功能。它通过 `NumCmp` trait 实现了不同类型数值（整数、浮点数、自定义的大整数引用）之间的安全比较操作，包括：
- 有符号/无符号整数比较
- 整数与浮点数比较，NaN 总是大于任何数值
- 原生类型与自定义的大整数引用（`BigUint`/`BigInt`）比较

`BigUint/BigInt` 为自定义的大整数引用类型，支持任意大小的整数比较，并优化了性能。特点：
- 为序列化后的二进制做优化，避免堆内存分配
- BigUint 直接借用大端字节、小端字节或 malachite::Natural，无需复制底层数据
- 和浮点数比较时， 分解浮点数的整数部分和小数部分，分别比较
- 大数库建议使用`malachite`库，性能远优于`num-bigint`库


## 功能特点

1. **跨类型比较**：
   - 支持所有原生整数类型（i8/u8/usize/isize 到 i128/u128）
   - 支持浮点数类型（f32/f64），NaN 总是大于任何数值
   - 支持自定义的大整数引用类型（`BigUint`/`BigInt`）

2. **完整的 `NumCmp` trait 比较操作**：
   ```rust
   pub trait NumCmp<Other: Copy>: Copy {
    fn num_cmp(self, other: Other) -> Ordering;
    fn num_eq(self, other: Other) -> bool;
    fn num_ne(self, other: Other) -> bool;
    fn num_lt(self, other: Other) -> bool;
    fn num_gt(self, other: Other) -> bool;
    fn num_le(self, other: Other) -> bool;
    fn num_ge(self, other: Other) -> bool;
   }
   ```

3. **正确处理特殊值**：
   - Float可比较, NaN 总是大于任何数值，和`order_float`库一致
   - 除NaN, INFINITY总是大于任何数值
   - NEG_INFINITY总是小于任何数值
   - 正确处理浮点数精度问题

4. **零开销抽象**：
   - 针对不同数值类型组合优化了实现策略
   - 避免堆内存分配
   - 内联优化关键路径

## 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
pi_num_cmp = "0.2"
```

## 使用示例

### 基本比较

```rust
use pi_num_cmp::NumCmp;
use std::cmp::Ordering;

// 不同类型数值比较
assert!(NumCmp::num_eq(3u64, 3.0f32));
assert!(NumCmp::num_lt(-4.7f64, -4i8));

// 浮点数精度处理
assert_eq!(NumCmp::num_cmp(40_000_000.0f32, 40_000_000u32), Ordering::Equal);
assert_ne!(NumCmp::num_cmp(40_000_001.0f32, 40_000_001u32), Ordering::Equal);

// NaN 处理
assert_eq!(NumCmp::num_cmp(f32::NAN, 40_000_002u32), Ordering::Greater);
```


### 从malachite的大整数转成自定义的大整数引用

```rust
use malachite::{Integer, Natural, platform::Limb};
use pi_num_cmp::NumCmp;
use pi_num_cmp::bigint::{BigUint, BigInt};

// 创建自定义的大整数引用
let natural = Natural::from(123456789012345678901234567890u128);
let mut limbs = natural.limbs();
let mut vec = Vec::with_capacity(limbs.len() * (Limb::BITS/u8::BITS) as usize);
// 先写高位，再写低位
while let Some(n) = limbs.next_back() {
    vec.extend_from_slice(&n.to_be_bytes());
}
assert_eq!(&vec, &[0, 0, 0, 1, 142, 233, 15, 246, 195, 115, 224, 238, 78, 63, 10, 210]);
// 创建自定义的大整数引用
let big_uint = BigUint::new(&vec);
assert_eq!(big_uint.bytes_be().collect::<Vec<_>>(), vec![1, 142, 233, 15, 246, 195, 115, 224, 238, 78, 63, 10, 210]);

// 原生类型与自定义大整数引用比较
assert!(NumCmp::num_gt(big_uint, 10000i16));
assert!(NumCmp::num_eq(123456789012345678901234567890u128, big_uint));
assert!(NumCmp::num_gt(big_uint, 123456789012345678901234567890.0 / 2.0));
assert!(NumCmp::num_lt(big_uint, 123456789012345678901234567890.0 * 2.0));
```

### 大整数支持

无需先转换成字节，推荐直接借用 Natural：

```rust
use malachite::Natural;
use pi_num_cmp::{bigint::BigUint, NumCmp};

let natural = Natural::from(65537u32);
let borrowed = BigUint::from_natural(&natural);
let be = BigUint::new(&[0, 1, 0, 1]);
let le = BigUint::from_le_bytes(&[1, 0, 1, 0]);
assert_eq!(borrowed, be);
assert_eq!(be, le);
assert!(borrowed.num_eq(65537u32));
assert_eq!(borrowed.bytes_be().collect::<Vec<_>>(), vec![1, 0, 1]);
```

BigUint 使用私有枚举存储大端字节、小端字节或 Natural，外部不能直接构造变体。
new 借用大端字节并裁掉头部零，from_le_bytes 借用小端字节并裁掉尾部零，
from_natural 直接借用已规范化的幅值。构造只缩短切片，不复制、不分配；低位零不会删除。
高位零只在构造时扫描，len 和 bytes_be 不重复扫描；字节构造仍支持 const。
as_be_bytes 和 as_natural 提供可选的只读借用访问，不允许改写内部存储。
Eq/Ord 按数值判定。bytes_be 返回高位优先、
可双向遍历的有效字节迭代器；仅在需要连续字节时由调用方显式 collect。
原 as_slice 已移除，因为 Natural 和小端视图不存在可直接返回的大端切片。
BigInt::new 为规范化任意视图的负零改为普通函数，不再支持 const 调用。

```rust
use pi_num_cmp::NumCmp;
use pi_num_cmp::bigint::{BigUint, BigInt};

// 创建自定义的大整数引用
let big_uint = BigUint::new(&[255, 254]); // 65534
let big_int = BigInt::new(BigUint::new(&[128]), false); // -128

// 原生类型与自定义大整数引用比较
assert!(NumCmp::num_eq(65534u32, big_uint));
assert!(NumCmp::num_gt(big_uint, 10000i16));

// 带符号比较
assert!(NumCmp::num_lt(big_int, 0i32));
assert!(NumCmp::num_lt(-129i16, big_int));
```

### 浮点数与大整数比较

```rust
use pi_num_cmp::NumCmp;
use pi_num_cmp::bigint::BigUint;

assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 15]), f32::MAX));
assert!(NumCmp::num_gt(BigUint::new(&[0xFF; 16]), f32::MAX));
assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 127]), f64::MAX));
assert!(NumCmp::num_gt(BigUint::new(&[0xFF; 128]), f64::MAX));
assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 256]), f32::INFINITY));
```

## 通用数值 Number

`Number` 是拥有数据的数值枚举，适合数据库记录、排序和哈希集合。与借用字节的 `bigint::BigInt` 不同，`Number::Integer` 直接持有 `malachite::Integer`。

```rust
pub enum Number {
    I64(i64),
    I128(i128),
    F64(f64),
    Integer(malachite::Integer),
}
```

### 比较与哈希

- `Eq`、`Ord`、`Hash` 按数值判断，不按变体区分；`I64(1)`、`I128(1)`、`F64(1.0)` 和大整数 1 相等且哈希一致。
- 正负零相等；所有 NaN 相等且大于正无穷；跨类型比较不先将整数转成浮点数，因此不会因浮点精度丢失而误判相等。
- 跨类型比较复用 `NumCmp`，两个 `Integer` 直接比较。`Number` 不是 `Copy`，不直接实现要求 `Copy` 的 `NumCmp`，请使用标准比较运算或 `cmp`。
- 哈希借用大整数的 limbs，不克隆幅值。哈希值不作为数据库的稳定编码或持久化标识。

```rust
use malachite::Integer;
use pi_num_cmp::Number;
use std::collections::HashSet;

let mut values = HashSet::new();
values.insert(Number::I64(1));
values.insert(Number::F64(1.0));
values.insert(Number::Integer(Integer::from(1)));
assert_eq!(values.len(), 1);
assert!(Number::I128(9_007_199_254_740_993) > Number::F64(9_007_199_254_740_992.0));
```

### 借用数值 NumberRef

`NumberRef<'a>` 包含 `I64`、`I128`、`F64`、`Integer(BigInt<'a>)` 四种变体，
实现 `Copy`、`Eq`、`Ord` 和 `NumCmp`。通过 `number.as_number_ref()` 可直接借用已有
`Number`，并支持与 `Number` 双向比较。所有比较复用本库的数字比较方法。

启用 `fory` 后，可以不构造 malachite 大整数，直接借用完整根消息中的幅值字节：

```rust
use malachite::Integer;
use pi_num_cmp::{Number, NumberRef};

let value = Number::Integer(Integer::from(1u8) << 256usize);
let mut writer = fory::Fory::builder().xlang(false).build();
writer.register_serializer::<Number>(100).unwrap();
let bytes = writer.serialize_with::<Number>(&value).unwrap();

// 读取器使用相同 ID 注册定位器，一次注册后可重复读取。
let mut reader = fory::Fory::builder().xlang(false).build();
NumberRef::register_fory(&mut reader, 100).unwrap();
let view = NumberRef::from_fory(&reader, &bytes).unwrap();
assert_eq!(view, value);
assert!(view > Number::I128(i128::MAX));
```

`from_fory` 使用 Fory 自身处理消息头和类型信息，不假定固定偏移。
读取端应使用单独的 Fory 实例，避免与相同 ID 的 `Number` serializer 冲突。
若调用方已经定位到自定义 serializer 的负载，使用 `read_fory_payload`，
返回视图和未消费尾部；不要把完整消息误当成负载。该负载读取只借用输入，
不分配幅值存储；完整消息的 Fory 注册和协议处理本身可能分配内存。
两种接口都会检查标签、符号和截断，借用视图不能超过原始缓冲的生命周期。
根消息接口不是任意嵌套字段的自动定位器；嵌套字段应在协议定位后读取负载。

### 四则运算

`+`、`-`、`*`、`/` 和对应的 `checked_add`、`checked_sub`、`checked_mul`、`checked_div` 消耗操作数，均返回 `Result<Number, NumberError>`。需要保留原值时由调用方显式克隆。

| 输入组合 | 结果规则 |
| --- | --- |
| 两个 I64 | 优先返回 I64，溢出后提升到 I128 |
| 含 I128 的原生整数 | 返回 I128，溢出后提升到 Integer |
| 含 Integer 的纯整数 | 使用 malachite 运算并保留 Integer，不自动缩回原生整数 |
| 任一操作数为 F64 | 返回 F64；整数转换为浮点数可能损失精度，溢出可得到无穷 |
| 纯整数除法 | 向零截断，例如 -7 / 2 = -3 |
| 任意类型的零除数 | 返回 NumberError::DivisionByZero，浮点正负零也报错 |

```rust
use pi_num_cmp::{Number, NumberError};

let sum = (Number::I64(i64::MAX) + Number::I64(1)).unwrap();
assert!(matches!(sum, Number::I128(_)));
assert_eq!((Number::I64(-7) / Number::I64(2)).unwrap(), Number::I64(-3));
assert_eq!(Number::I64(1).checked_div(Number::F64(-0.0)), Err(NumberError::DivisionByZero));
```

原生整数未溢出时不创建临时大整数。已有大整数按值移交，允许 malachite 复用底层缓冲；原生整数与大整数混算时需构造 malachite 操作数。大整数跨类型比较直接通过 BigUint::from_natural 借用幅值，不再创建临时 Vec 或 Integer。

### 可选序列化

默认不启用序列化，`serde` 和 `fory` 可分别或同时启用：

```toml
[dependencies]
pi_num_cmp = { version = "0.2", features = ["serde", "fory"] }
```

`serde` 提供 `Serialize` / `Deserialize`，保留枚举变体，并使用 malachite 的大整数序列化表示。具体格式由所选 Serde 后端决定；JSON 不支持 NaN 和无穷的无损往返，请使用支持这些值的格式或限制数据范围。

`fory` 使用自定义 serializer，当前按 Rust 原生模式配置，不承诺跨语言或长期字节格式稳定：

```rust
use pi_num_cmp::Number;

let mut fory = fory::Fory::builder().xlang(false).build();
fory.register_serializer::<Number>(100).unwrap();
let bytes = fory.serialize_with::<Number>(&Number::I64(42)).unwrap();
let decoded = fory.deserialize_with::<Number>(&bytes).unwrap();
assert_eq!(decoded, Number::I64(42));
```

上例要求应用直接依赖 `fory = "1.7"`，注册 ID 由应用统一分配。嵌套于应用结构字段时，按 Fory 的自定义 serializer 方式指定 `#[fory(with = Number)]`。Fory 1.7.7 在当前 32 位 Windows 工具链上存在上游编译限制，完整功能已在 64 位 Windows MSVC 工具链验证。

malachite 使用 LGPL-3.0 许可证；分发包含本库的程序时请同时核对依赖许可证义务。替换大整数后，`Integer` 的 Serde 表示与旧 num-bigint 版本不同，旧数据需由应用迁移，不能假设直接兼容。

## 性能特点

`pi_num_cmp` 针对不同数值类型组合实现了多种优化策略：

1. **直接比较**：相同类型时使用原生比较操作
2. **安全转换**：可无损转换时进行安全类型转换
3. **符号处理**：优化有符号/无符号类型比较
4. **边界检查**：处理浮点数的整数表示边界
5. **大整数优化**：
   - 避免堆内存分配
   - 使用前缀比较优化
   - 特殊处理常见位宽（64/128位）

## 应用场景

1. 科学计算和数值分析
2. 财务计算和货币处理
3. 数据验证和边界检查
4. 自定义数据结构中的值比较
5. 序列化后的数值比较

## 贡献指南

欢迎贡献！请遵循以下步骤：

1. 提交 issue 描述问题或新功能建议
2. Fork 仓库并创建特性分支
3. 添加测试用例覆盖所有修改
4. 运行测试：`cargo test --all-features`
5. 提交 pull request

## 许可证

本项目采用 MIT 许可证 - 详见 [LICENSE](LICENSE) 文件。
