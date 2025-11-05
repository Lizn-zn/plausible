import Plausible

/-!
# 性能测试示例

本文件包含一些示例，展示优化后的 Plausible 性能。

## 测试不同配置的性能差异
-/

-- 示例 1: 列表属性测试
-- 这个属性是错误的，会触发收缩过程
example : ∀ (xs : List Nat), xs.length < 5 := by
  -- 使用快速配置
  plausible (config := { Configuration.fast with quiet := false })
  sorry

-- 示例 2: 数组属性测试
example : ∀ (xs : Array Int), xs.size = 0 ∨ xs[0]! ≥ 0 := by
  -- 使用最小配置
  plausible (config := { Configuration.minimal with quiet := false })
  sorry

-- 示例 3: 字符串属性测试
example : ∀ (s : String), s.length < 10 := by
  -- 使用默认配置
  plausible
  sorry

-- 示例 4: 嵌套列表测试
example : ∀ (xss : List (List Nat)), xss.length < 3 := by
  -- 使用自定义配置，限制大小和收缩深度
  plausible (config := { numInst := 10, maxSize := 20, maxShrinkDepth := some 10 })
  sorry

/-!
## 性能比较

要比较不同配置的性能，可以使用 #time 命令：

```lean
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) Configuration.minimal
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) Configuration.fast
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) {}  -- 默认配置
```

## 测试收缩优化

下面的属性会找到一个反例并进行收缩：
-/

-- 这会找到反例并演示优化后的收缩过程
#eval Testable.check
  (∀ (xs : List Nat), xs.sum < 100)
  { Configuration.fast with traceShrink := true }

-- 这个例子展示了对大数组的优化收缩
#eval Testable.check
  (∀ (xs : Array Nat), xs.size < 10)
  { Configuration.fast with traceShrink := true }

/-!
## 内存使用优化

以下示例展示了生成大小限制如何防止内存问题：

在优化前，这可能会尝试生成非常大的列表。
优化后，列表大小被限制在合理范围内。
-/

-- 测试列表生成的大小限制
#eval do
  let xs : List Nat ← Gen.run (Gen.listOf Arbitrary.arbitrary (maxSize := some 50)) 100
  IO.println s!"Generated list of length: {xs.length}"

-- 测试数组生成的大小限制
#eval do
  let xs : Array Nat ← Gen.run (Gen.arrayOf Arbitrary.arbitrary (maxSize := some 50)) 100
  IO.println s!"Generated array of size: {xs.size}"

/-!
## 建议的测试策略

1. **开发阶段**: 使用 `Configuration.fast` 快速迭代
2. **CI 流水线**: 使用 `Configuration.minimal` 进行快速健全性检查
3. **夜间构建**: 使用默认或更严格的配置进行全面测试
4. **调试失败**: 使用 `Configuration.verbose` 查看详细信息
-/
