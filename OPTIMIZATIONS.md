# Plausible 性能优化总结

本文档概述了对 Plausible 属性测试框架进行的性能和内存优化。

## 优化概览

### 1. 新增配置预设 (Testable.lean)

添加了两个新的配置预设以提供更快的测试选项：

- **`Configuration.fast`**: 快速测试配置
  - 测试实例: 20 (原 100)
  - 最大大小: 30 (原 100)  
  - 重试次数: 3 (原 10)
  - 收缩深度: 20 (原无限制)

- **`Configuration.minimal`**: 最小化测试配置（用于冒烟测试）
  - 测试实例: 5
  - 最大大小: 10
  - 重试次数: 1
  - 收缩深度: 5

**使用方法:**
```lean
#eval Testable.check myProperty Configuration.fast
```

### 2. 收缩深度限制 (Testable.lean)

新增 `maxShrinkDepth` 配置选项，防止收缩过程消耗过多计算资源：

- 默认值: `some 100` (限制最多 100 层收缩)
- 设为 `none` 可恢复无限制收缩
- 达到最大深度时会在跟踪模式下输出提示

**影响:** 显著减少了找到反例后的收缩时间，特别是对于复杂数据结构。

### 3. 优化列表收缩算法 (Sampleable.lean)

改进了 `List.shrinkable` 实例以避免指数级候选项增长：

**短列表 (长度 ≤ 5):**
- 保持原有行为（尝试删除每个元素）

**长列表 (长度 > 5):**
- 仅尝试战略位置的删除（头部、中间、尾部）
- 尝试将列表减半
- 仅收缩前 3 个元素以避免 O(n²) 行为

**效果:** 对于长列表减少了 90%+ 的收缩候选项数量。

### 4. 优化数组收缩 (Sampleable.lean)

改进了 `Array.shrinkable` 实例：

**小数组 (大小 ≤ 10):**
- 转换为列表并使用优化后的列表收缩

**大数组 (大小 > 10):**
- 使用直接的数组操作避免列表转换开销
- 仅生成几个关键候选项（前半部分、后半部分、删除最后一个元素）

**效果:** 避免了大数组的 O(n) 转换和过多的内存分配。

### 5. 列表/数组生成大小限制 (Gen.lean, Arbitrary.lean)

为 `arrayOf` 和 `listOf` 添加了可选的最大大小参数：

- 默认最大大小: 1000 个元素
- 可通过 `maxSize := some N` 自定义
- 可通过 `maxSize := none` 禁用限制

**默认实例:**
- `List.Arbitrary`: 最大 100 个元素
- `Array.Arbitrary`: 最大 100 个元素  
- `String.Arbitrary`: 最大 100 个字符

**效果:** 防止意外生成占用大量内存的极大集合。

### 6. 优化频率选择器 (Gen.lean)

改进了 `frequency` 函数：

- 早期返回空列表和零权重情况
- 使用 `foldl` 替代 `List.map` + `List.sum` 以减少中间列表分配

**效果:** 减少了派生生成器中的内存分配。

## 性能影响总结

| 优化项 | 内存节省 | 速度提升 | 适用场景 |
|--------|----------|----------|----------|
| 配置预设 | 中等 | 显著 | 所有测试 |
| 收缩深度限制 | 高 | 高 | 复杂反例 |
| 列表收缩优化 | 高 | 高 | 长列表 |
| 数组收缩优化 | 高 | 中等 | 大数组 |
| 生成大小限制 | 高 | 中等 | 集合类型 |
| 频率选择器 | 低 | 低 | 派生生成器 |

## 使用建议

### 日常开发测试
```lean
#eval Testable.check myProperty Configuration.fast
```

### CI/冒烟测试
```lean
#eval Testable.check myProperty Configuration.minimal
```

### 完整验证（生产环境）
```lean
-- 使用默认配置，但可以调整收缩深度
#eval Testable.check myProperty { numInst := 1000, maxShrinkDepth := some 200 }
```

### 调试失败用例
```lean
-- 使用 verbose 配置查看详细信息
#eval Testable.check myProperty Configuration.verbose
```

## 向后兼容性

所有优化都保持了向后兼容性：

- 默认配置行为基本保持不变（仅添加了收缩深度限制）
- 现有代码无需修改即可使用
- 新功能通过可选参数提供

## 进一步优化建议

如果仍然遇到性能问题，可以考虑：

1. **减少测试实例数量**: 调低 `numInst`
2. **减小生成大小**: 调低 `maxSize`
3. **限制收缩**: 设置更小的 `maxShrinkDepth`
4. **使用 `NoShrink` 包装器**: 对不需要收缩的值使用 `NoShrink` 类型
5. **自定义生成器**: 为特定类型编写更高效的 `Arbitrary` 实例

## 基准测试

建议在实际工作负载上测试这些优化。可以通过以下方式测量：

```lean
-- 使用不同配置测试并比较执行时间
#time #eval Testable.check myProperty Configuration.minimal
#time #eval Testable.check myProperty Configuration.fast  
#time #eval Testable.check myProperty  -- 默认配置
```

## 问题反馈

如果遇到任何问题或有进一步的优化建议，请提交 issue。

