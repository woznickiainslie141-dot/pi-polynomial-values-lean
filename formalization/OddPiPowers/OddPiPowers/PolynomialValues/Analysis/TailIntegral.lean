module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! All interval formulas used by the compact prime-cost certificates are exact. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory
open scoped Interval

theorem integral_affine_real (l r A B : ℝ) :
    (∫ y in l..r, A + B * y) = (r-l) * (A + B*(l+r)/2) := by
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => A) (g := fun y : ℝ => B*y) intervalIntegrable_const
    ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul B (fun y : ℝ => y),
    integral_id, smul_eq_mul]
  ring

/-- Integrated height of one row or column above the moving level k y. -/
noncomputable def tailIntegralReal (w k l r : ℝ) : ℝ :=
  if k = 0 then w * (r-l)
  else ((max 0 (w-k*l))^2 - (max 0 (w-k*r))^2) / (2*k)

theorem integral_tail_real (w k l r : ℝ) (hw : 0 ≤ w) (hk' : 0 ≤ k) (hlr : l ≤ r) :
    (∫ y in l..r, max 0 (w-k*y)) = tailIntegralReal w k l r := by
  rcases eq_or_lt_of_le hk' with h | hk
  · subst k
    simp [tailIntegralReal, max_eq_right hw, smul_eq_mul, mul_comm]
  rw [tailIntegralReal, if_neg hk.ne']
  have active (a b : ℝ) (hab : a ≤ b) (h : k*b ≤ w) :
      (∫ y in a..b, max 0 (w-k*y)) = (b-a)*(w+(-k)*(a+b)/2) := by
    calc
      _ = ∫ y in a..b, w+(-k)*y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le hab] at hy
        change max 0 (w-k*y) = w+(-k)*y
        rw [max_eq_right (sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hy.2 hk.le).trans h))]
        ring
      _ = _ := integral_affine_real a b w (-k)
  have inactive (a b : ℝ) (hab : a ≤ b) (h : w ≤ k*a) :
      (∫ y in a..b, max 0 (w-k*y)) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le hab] at hy
        exact max_eq_left (sub_nonpos.mpr (h.trans (mul_le_mul_of_nonneg_left hy.1 hk.le)))
      _ = _ := by simp
  have hkr := mul_le_mul_of_nonneg_left hlr hk.le
  by_cases hleft : w ≤ k*l
  · rw [inactive l r hlr hleft, max_eq_left (sub_nonpos.mpr hleft),
      max_eq_left (sub_nonpos.mpr (hleft.trans hkr))]
    simp
  by_cases hright : k*r ≤ w
  · rw [active l r hlr hright, max_eq_right (sub_nonneg.mpr (hkr.trans hright)),
      max_eq_right (sub_nonneg.mpr hright)]
    field_simp [hk.ne'] <;> ring
  let t := w/k
  have hc : k*t = w := by dsimp [t]; field_simp [hk.ne']
  have hlt : l ≤ t := by
    apply (le_div_iff₀ hk).mpr
    simpa only [mul_comm] using (lt_of_not_ge hleft).le
  have htr : t ≤ r := by
    apply (div_le_iff₀ hk).mpr
    simpa only [mul_comm] using (lt_of_not_ge hright).le
  have hc' : Continuous (fun y : ℝ => max 0 (w-k*y)) :=
    continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc'.intervalIntegrable l t)
    (hc'.intervalIntegrable t r), active l t hlt hc.le, inactive t r htr hc.ge,
    add_zero, max_eq_right (sub_nonneg.mpr (lt_of_not_ge hleft).le),
    max_eq_left (sub_nonpos.mpr (lt_of_not_ge hright).le)]
  dsimp [t]
  field_simp [hk.ne'] <;> ring

end PiPolynomialValues
