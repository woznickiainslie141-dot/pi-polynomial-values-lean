module

public import OddPiPowers.PolynomialValues.Analysis.FoldedSine
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integrating a finite geometric series bounds the two actual arc primitives. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Real

def arcGeom (s : ℝ) (n : ℕ) (t : ℝ) : ℝ := ∑ i ∈ Finset.range n, (s*t^2)^i

def arcOdd {K : Type*} [Field K] (s : K) (n : ℕ) (x : K) : K :=
  ∑ i ∈ Finset.range n, s^i*x^(2*i+1)/((2*i+1 : ℕ) : K)

private theorem geom_gap (s t : ℝ) (n : ℕ) (h : 1-s*t^2 ≠ 0) :
    1/(1-s*t^2)-arcGeom s n t = (s*t^2)^n/(1-s*t^2) := by
  apply (eq_div_iff h).mpr
  rw [sub_mul, div_mul_cancel₀ _ h, arcGeom, geom_sum_mul_neg]
  ring

private theorem arcGeom_integral (s x : ℝ) (n : ℕ) :
    (∫ t in 0..x, arcGeom s n t) = arcOdd s n x := by
  unfold arcGeom arcOdd
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (by fun_prop : Continuous (fun t : ℝ => (s*t^2)^i)).intervalIntegrable 0 x)]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_pow, ← pow_mul]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [Nat.cast_add, Nat.cast_one, zero_pow (Nat.succ_ne_zero _), sub_zero]
  ring

private theorem primitive_bounds {s x c : ℝ} {n : ℕ} {f : ℝ → ℝ} (hx : 0 ≤ x)
    (hf : IntervalIntegrable f volume 0 x)
    (h : ∀ t ∈ Set.Icc 0 x, 0 ≤ f t-arcGeom s n t ∧ f t-arcGeom s n t ≤ c*t^(2*n)) :
    arcOdd s n x ≤ (∫ t in 0..x, f t) ∧
      (∫ t in 0..x, f t) ≤ arcOdd s n x+c*x^(2*n+1)/((2*n+1 : ℕ) : ℝ) := by
  have hc : Continuous (arcGeom s n) := by unfold arcGeom; fun_prop
  have hp : Continuous (fun t : ℝ => c*t^(2*n)) := by fun_prop
  have hl := intervalIntegral.integral_mono_on (μ := volume) hx (hc.intervalIntegrable _ _) hf
    (fun t ht => sub_nonneg.mp (h t ht).1)
  have hu := intervalIntegral.integral_mono_on (μ := volume) hx hf
    ((hc.add hp).intervalIntegrable 0 x) (fun t ht => by
      have := (h t ht).2
      change f t ≤ arcGeom s n t + c*t^(2*n)
      linarith)
  rw [arcGeom_integral] at hl
  change (∫ t in 0..x, f t) ≤ (∫ t in 0..x, arcGeom s n t+c*t^(2*n)) at hu
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    arcGeom_integral, intervalIntegral.integral_const_mul, integral_pow] at hu
  refine ⟨hl, ?_⟩
  convert hu using 1
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one]
  ring

theorem arctan_ten_bounds {x : ℝ} (hx : 0 ≤ x) :
    arcOdd (-1) 10 x ≤ arctan x ∧ arctan x ≤ arcOdd (-1) 10 x+x^21/21 := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) :=
    continuous_const.div (by fun_prop) (fun t => by positivity)
  have h := primitive_bounds (s := -1) (n := 10) (c := 1) hx (hc.intervalIntegrable 0 x) (by
    intro t ht
    have hd : 0 < 1+t^2 := by positivity
    have hr := geom_gap (-1) t 10 (by simpa using hd.ne')
    have hpow : (-1*t^2)^10 = t^20 := by ring
    rw [hpow] at hr
    simp only [neg_one_mul, sub_neg_eq_add] at hr
    rw [hr]
    constructor
    · positivity
    · simpa using div_le_div_of_nonneg_left (show 0 ≤ t^20 by positivity)
        (show (0 : ℝ) < 1 by norm_num) (show 1 ≤ 1+t^2 by nlinarith [sq_nonneg t]))
  rw [integral_one_div_one_add_sq, arctan_zero, sub_zero] at h
  norm_num at h ⊢
  exact h

theorem halfLogRatio_odd_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    arcOdd 1 n x ≤ halfLogRatio x ∧ halfLogRatio x ≤
      arcOdd 1 n x + x^(2*n+1)/(((2*n+1 : ℕ) : ℝ)*(1-x^2)) := by
  have hp : 0 < 1-x^2 := by nlinarith [mul_pos (sub_pos.mpr hx1) (show 0 < 1+x by linarith)]
  have den (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : 0 < 1-t^2 := by
    rw [Set.uIcc_of_le hx] at ht
    have hv := pow_le_pow_left₀ ht.1 ht.2 2
    linarith
  have hc : ContinuousOn (fun t : ℝ => 1/(1-t^2)) (Set.uIcc 0 x) :=
    continuousOn_const.div (by fun_prop) (fun t ht => (den t ht).ne')
  have h := primitive_bounds (s := 1) (n := n) (c := 1/(1-x^2)) hx hc.intervalIntegrable (by
    intro t ht
    have hv := pow_le_pow_left₀ ht.1 ht.2 2
    have hd : 0 < 1-t^2 := by linarith
    have hr := geom_gap 1 t n (by simpa using hd.ne')
    simp only [one_mul, ← pow_mul] at hr
    rw [hr]
    constructor
    · exact div_nonneg (pow_nonneg ht.1 _) hd.le
    · simpa [div_eq_mul_inv, mul_comm] using
        div_le_div_of_nonneg_left (pow_nonneg ht.1 (2*n)) hp (show 1-x^2 ≤ 1-t^2 by linarith))
  have hi : (∫ t : ℝ in 0..x, 1/(1-t^2)) = halfLogRatio x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := halfLogRatio) (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact hasDerivAt_halfLogRatio (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hx1))
      hc.intervalIntegrable]
    simp [halfLogRatio]
  rw [hi] at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

end PiPolynomialValues
