import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import EMath.Defs
import EMath.Algebra.Trigonometric.Problem3

/-!
desc: Show that `π` is fundamental period of `cot(x)`.
difficulty: 1
authro: zqc17
comments: `cot(x)` was not defined in Mathlib, just use `1/tan(x)`.
-/

open Real Function

/-- `π` is fundamental period of `cot(x)`. -/
theorem cot_fundamental_period : IsFundamentalPeriod (fun x => (tan x)⁻¹) π := by
  rw [IsFundamentalPeriod.inv_iff]
  exact tan_fundamental_period
