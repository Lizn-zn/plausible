import Plausible

set_option maxHeartbeats 0
set_option trace.plausible.decoration true

-- 简单测试：看看转换是否工作
example : ∀ (l : List Nat), (∀ d ∈ l, d < 10) → True := by
  plausible (config := {numInst := 10})
