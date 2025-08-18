

# pi_num_cmp

[![Crates.io](https://img.shields.io/crates/v/pi_num_cmp)](https://crates.io/crates/pi_num_cmp)
[![Documentation](https://docs.rs/pi_num_cmp/badge.svg)](https://docs.rs/pi_num_cmp)

`pi_num_cmp` 是一个 Rust 库，提供了跨类型数值比较功能。它通过 `NumCmp` trait 实现了不同类型数值（整数、浮点数、自定义的大整数引用）之间的安全比较操作，包括：
- 有符号/无符号整数比较
- 整数与浮点数比较，NaN 总是大于任何数值
- 原生类型与自定义的大整数引用（`BigUint`/`BigInt`）比较

`BigUint/BigInt` 为自定义的大整数引用类型，支持任意大小的整数比较，并优化了性能。特点：
- 为序列化后的二进制做优化，避免堆内存分配
- 要求参数为字节数组引用，大整数在字节数组中高位在前，低位在后
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
pi_num_cmp = "0.1"
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
use pi_num_cmp::{NumCmp, BigUint, BigInt};

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
assert_eq!(big_uint.as_slice(), &[1, 142, 233, 15, 246, 195, 115, 224, 238, 78, 63, 10, 210]);

// 原生类型与自定义大整数引用比较
assert!(NumCmp::num_gt(big_uint, 10000i16));
assert!(NumCmp::num_eq(123456789012345678901234567890u128, big_uint));
assert!(NumCmp::num_gt(big_uint, 123456789012345678901234567890.0 / 2.0));
assert!(NumCmp::num_lt(big_uint, 123456789012345678901234567890.0 * 2.0));
```

### 大整数支持

```rust
use pi_num_cmp::{NumCmp, BigUint, BigInt};

// 创建自定义的大整数引用
let big_uint = BigUint::new(&[255, 254]); // 65534
let big_int = BigInt::new(BigUint::new(&[128]), false); // -128

// 原生类型与自定义大整数引用比较
assert!(NumCmp::num_eq(65534u32, big_uint));
assert!(NumCmp::num_gt(big_uint, 10000i16));

// 带符号比较
assert!(NumCmp::num_lt(big_int, 0i32));
assert!(NumCmp::num_ge(-129i16, big_int));
```

### 浮点数与大整数比较

```rust
use pi_num_cmp::{NumCmp, BigUint};

assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 15]), f32::MAX));
assert!(NumCmp::num_gt(BigUint::new(&[0xFF; 16]), f32::MAX));
assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 127]), f64::MAX));
assert!(NumCmp::num_gt(BigUint::new(&[0xFF; 128]), f64::MAX));
assert!(NumCmp::num_lt(BigUint::new(&[0xFF; 256]), f32::INFINITY));
```

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
