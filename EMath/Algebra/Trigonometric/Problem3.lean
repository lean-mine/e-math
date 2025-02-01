import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import EMath.Defs

/-!
desc: Show that `π` is fundamental period of `tan(x)`.
difficulty: 2
authro: zqc17
comments: `tan(x)` in Mathlib is slightly different from the one in textbook since it satisfies:
  `$tan(kπ+π/2)=0$` where `k` is arbitrary integer.
-/

open Real Function

/-- `π` is fundamental period of `tan(x)`. -/
theorem tan_fundamental_period : IsFundamentalPeriod tan π := by
  constructor
  . -- Firstly, we show that `π` is positive and a period of `tan(x)`.
    constructor
    . -- It's clear that `π` is positive.
      positivity
    -- It's clear that `π` is a period of `tan(x)`.
    exact tan_periodic
  -- Now, we show that `π` is the smallest positive period of `tan(x)`.
  intro c ⟨hcpos, hcperiod⟩
  -- We can assume `c < π` and then prove by contradiction.
  by_contra! h
  -- Since `c` is a period of `tan(x)`, we have `tan(-c/2+c) = tan(-c/2)`.
  specialize hcperiod (-c / 2)
  -- Which can be simplified to `tan(-c/2) = tan(c/2)`.
  rw [show -c / 2 + c = c / 2 by ring] at hcperiod
  -- It suffices to show that `tan(-c/2) < tan(c/2)`.
  suffices tan (-c / 2) < tan (c / 2) by linarith
  -- This is obvious since `tan(x)` is strictly monotone on `(-π/2,π/2)`.
  apply strictMonoOn_tan
  -- We can show that `-c/2` and `c/2` are located in the interval `(-π/2,π/2)` and
  -- `-c/2 < c/2` by simple calculation.
  any_goals split_ands
  all_goals linarith
