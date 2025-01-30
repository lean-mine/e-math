import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Periodic
import Mathlib.Order.Bounds.Defs

namespace Function

/-- The least value of the positive real number c is called the fundamental period of a function. -/
def IsFundamentalPeriod (f : ℝ → ℝ) (c : ℝ) : Prop :=
  IsLeast {c : ℝ | 0 < c ∧ f.Periodic c} c

/-- If `c` is fundamental period of `f`, then `c` is a period of `f`. -/
theorem IsFundamentalPeriod.periodic {f : ℝ → ℝ} {c : ℝ} (h : f.IsFundamentalPeriod c) :
    f.Periodic c := h.1.2

/-- If `c` is fundamental period of `f`, then `c` is positive. -/
theorem IsFundamentalPeriod.pos {f : ℝ → ℝ} {c : ℝ} (h : f.IsFundamentalPeriod c) : 0 < c := h.1.1

/-- `c` is a period of `f(x)` if and only if `c` is a period of `f(x+a)`. -/
theorem Periodic.add_const_iff {f : ℝ → ℝ} {c : ℝ} {a : ℝ} :
    (fun x => f (x + a)).Periodic c ↔ f.Periodic c := by
  refine ⟨fun h => ?_, fun h => Periodic.add_const h a⟩
  convert Periodic.add_const h (-a)
  rw [neg_add_cancel_right]

/-- Fundamental period is invariant under translation. -/
theorem IsFundamentalPeriod.add_const {f : ℝ → ℝ} {c : ℝ} (h : f.IsFundamentalPeriod c) (a : ℝ) :
    (fun x => f (x + a)).IsFundamentalPeriod c := by
  constructor
  . refine ⟨h.pos, ?_⟩
    apply Periodic.add_const
    exact h.periodic
  conv_lhs => rhs; rhs; intro c; rw [Periodic.add_const_iff]
  exact h.2

/-- `c` is fundamental period of `f(x)` if and only if `c` is fundamental period of `f(x+a)`. -/
theorem IsFundamentalPeriod.add_const_iff {f : ℝ → ℝ} {c : ℝ} {a : ℝ} :
    (fun x => f (x + a)).IsFundamentalPeriod c ↔ f.IsFundamentalPeriod c := by
  refine ⟨fun h => ?_, fun h => IsFundamentalPeriod.add_const h a⟩
  convert IsFundamentalPeriod.add_const h (-a)
  rw [neg_add_cancel_right]

end Function
