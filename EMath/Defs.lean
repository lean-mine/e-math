import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Periodic
import Mathlib.Order.Bounds.Defs

namespace Function

/-- If `c` is a period of `f(x)`, then `c` is a period of `f(x)⁻¹`. -/
theorem Periodic.inv_real {f : ℝ → ℝ} {c : ℝ} (h : f.Periodic c) :
    (fun x => (f x)⁻¹).Periodic c := by
  intro x
  rw [inv_inj]
  exact h x

/-- `c` is a period of `f(x)` if and only if `c` is a period of `f(x)⁻¹`. -/
theorem Periodic.inv_iff_real {f : ℝ → ℝ} {c : ℝ} : (fun x => (f x)⁻¹).Periodic c ↔
    f.Periodic c := by
  refine ⟨fun h => ?_, fun h => Periodic.inv_real h⟩
  convert Periodic.inv_real h using 1
  conv => rhs; intro x; rw [inv_inv]

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

/-- Fundamental period is invariant under `inv`. -/
theorem IsFundamentalPeriod.inv {f : ℝ → ℝ} {c : ℝ} (h : f.IsFundamentalPeriod c) :
    (fun x => (f x)⁻¹).IsFundamentalPeriod c := by
  constructor
  . refine ⟨h.pos, ?_⟩
    exact h.periodic.inv_real
  conv_lhs => rhs; rhs; intro c; rw [Periodic.inv_iff_real]
  exact h.2

/-- `c` is fundamental period of `f(x)` if and only if `c` is fundamental period of `f(x)⁻¹`. -/
theorem IsFundamentalPeriod.inv_iff {f : ℝ → ℝ} {c : ℝ} : (fun x => (f x)⁻¹).IsFundamentalPeriod c ↔
    f.IsFundamentalPeriod c := by
  refine ⟨fun h => ?_, fun h => IsFundamentalPeriod.inv h⟩
  convert IsFundamentalPeriod.inv h using 1
  conv => rhs; intro x; rw [inv_inv]

end Function
