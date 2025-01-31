import Mathlib
import EMath.Defs

/-!
desc: Show that `2π` is fundamental period of `sin(x)`.
difficulty: 2
authro: zqc17
-/

open Real Function

/-- `2π` is fundamental period of `sin(x)`. -/
theorem sin_fundamental_period : IsFundamentalPeriod sin (2 * π) := by
  constructor
  . -- Firstly, we show that `2π` is positive and a period of `sin(x)`.
    constructor
    . -- It's clear that `2π` is positive.
      linarith [pi_pos]
    -- It's clear that `2π` is a period of `sin(x)`.
    exact sin_periodic
  -- Now, we show that `2π` is the smallest positive period of `sin(x)`.
  intro c ⟨hcpos, hcperiod⟩
  -- We can assume `c < 2π` and then prove by contradction.
  by_contra! h
  -- Since `c` is a period of `sin(x)`, we have `sin(π/2 + c) = sin(π/2)`.
  specialize hcperiod (π / 2)
  rw [
    -- Which can be simplified to `sin(π/2 + c) = 1`.
    sin_pi_div_two,
    -- Using `sin_eq_one_iff`, there exists integer `k` such that `π/2 + 2kπ = π/2 + c`.
    -- We will show this is impossible since `c < 2π`.
    sin_eq_one_iff] at hcperiod
  rcases hcperiod with ⟨k, hk⟩
  -- We split into 3 cases.
  rcases lt_trichotomy k 0 with h | h | h
  . -- Case (1): `k < 0`
    -- Notice that `k` is an integer, we can deduce `k≤-1` from `k<0`.
    have : k ≤ -1 := by omega
    -- Hence we have `2kπ ≤ -2π`.
    have : k * (2 * π) ≤ (-1) * (2 * π) := by gcongr; assumption_mod_cast
    -- Which is contradictory to previous conclustion that `π/2 + 2kπ = π/2 + c`.
    linarith
  . -- Case (2): `k = 0`
    -- We can deduce that `c=0`.
    norm_num [h] at hk
    -- This is impossible since `c` is positive.
    norm_num [hk] at hcpos
  -- Case (3): `0 < k`
  -- Notice that `k` is an integer, we can deduce `1≤k` from `0<k`.
  have : 1 ≤ k := by omega
  -- Hence we have `2π ≤ 2kπ`.
  have : 1 * (2 * π) ≤ k * (2 * π) := by gcongr; assumption_mod_cast
  -- Which is contradictory to previous conclustion that `π/2 + 2kπ = π/2 + c`.
  linarith
