module

public import OddPiPowers.PolynomialValues.Analysis.PoissonComparison
public import OddPiPowers.PolynomialValues.RootDistances
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Reverse

/-! A bound for the polynomial on the unit circle simultaneously
bounds its normalized evaluation at every complex conjugate. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Metric Polynomial

theorem polynomial_disk_bound (P : ℂ[X]) {C : ℝ} (hc : ∀ z : ℂ, ‖z‖=1 → ‖P.eval z‖≤C)
    {z : ℂ} (hz : ‖z‖≤1) : ‖P.eval z‖≤C := by
  rcases hz.lt_or_eq with h|h
  · exact analytic_unit_norm_bound h ((AnalyticOnNhd.eval_polynomial P).mono (Set.subset_univ _))
      (fun y hy => hc y (by simpa [mem_sphere,dist_eq_norm] using hy))
  · exact hc _ h

theorem norm_reverse_at_inv (P : ℂ[X]) {z : ℂ} (hz : z≠0) :
    ‖P.reverse.eval z⁻¹‖*‖z‖^P.natDegree=‖P.eval z‖ := by
  letI : Invertible z := invertibleOfNonzero hz
  have H := eval₂_reverse_mul_pow (RingHom.id ℂ) z P
  rw [invOf_eq_inv] at H
  simpa only [eval₂_id,norm_mul,norm_pow] using congrArg norm H

theorem polynomial_normalized_bound (P : ℂ[X]) {C : ℝ} (hc : ∀ z : ℂ, ‖z‖=1 → ‖P.eval z‖≤C) (z : ℂ) :
    ‖P.eval z‖/(rootScale z)^P.natDegree≤C := by
  rcases le_or_gt ‖z‖ 1 with hz|hz
  · simpa [rootScale,max_eq_left hz] using polynomial_disk_bound P hc hz
  · have hn : z≠0 := fun he => by simp [he] at hz; linarith
    have hrev (y : ℂ) (hy : ‖y‖=1) : ‖P.reverse.eval y‖≤C := by
      have hy0 : y≠0 := fun he => by simp [he] at hy
      have H := norm_reverse_at_inv P (inv_ne_zero hy0)
      simp only [inv_inv,norm_inv,hy,inv_one,one_pow,mul_one] at H
      exact H.le.trans (hc y⁻¹ (by simp [hy]))
    have hzinv : ‖z⁻¹‖≤1 := by rw [norm_inv]; exact (inv_le_one₀ (norm_pos_iff.mpr hn)).mpr hz.le
    have H := polynomial_disk_bound P.reverse hrev hzinv
    rw [rootScale,max_eq_right hz.le,← norm_reverse_at_inv P hn,mul_div_cancel_right₀ _
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))]
    exact H

end PiPolynomialValues
