import Mathlib
import EMath.Defs
import EMath.Algebra.Trigonometric.Problem1

/-!
desc: Show that `2π` is fundamental period of `cos(x)`.
difficulty: 1
authro: zqc17
comments: Given `2π` is fundamental period of `sin(x)`, this is easy since `cos(x) = sin(x+π/2)`.
-/

open Real Function

/-- `2π` is fundamental period of `cos(x)`. -/
theorem cos_fundamental_period : IsFundamentalPeriod cos (2 * π) := by
  -- Notice that `cos(x) = sin(x+π/2)`.
  conv_lhs => ext x; rw [← sin_add_pi_div_two]
  -- Notice that `sin(x+π/2)` has the same fundamental period as `sin(x)`.
  rw [IsFundamentalPeriod.add_const_iff]
  -- We have proved the period of `sin(x)` already.
  exact sin_fundamental_period
