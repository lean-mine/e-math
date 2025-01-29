import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant

/-!
desc: Show that if discriminant of quadratic equation $ax^2+bx+c=0$ is non-negtive then
  $x_1,x_2=\frac{-b\pm\sqrt{b^2-4ac}}{2a}$ are roots of the equation.
difficulty: 1
authro: zqc17
-/

/-- Roots of a quadratic equation. This is a consequence of `quadratic_eq_zero_iff`. -/
theorem quadratic_eq_zero_iff_real {a b c : ℝ} (ha : a ≠ 0)
    (hdiscrim : 0 ≤ discrim a b c) (x : ℝ) :
    a * x ^ 2 + b * x + c = 0 ↔ x = (-b + √(discrim a b c)) / (2 * a) ∨
    x = (-b - √(discrim a b c)) / (2 * a) := by
  rw [
    -- x ^ 2 = x * x
    pow_two,
    -- Use the general version of quadratic formula.
    quadratic_eq_zero_iff ha]
  -- It's clear that `discrim a b c = √(discrim a b c) * √(discrim a b c)`
  -- since `discrim a b c` is non-negtive.
  exact (Real.mul_self_sqrt hdiscrim).symm
