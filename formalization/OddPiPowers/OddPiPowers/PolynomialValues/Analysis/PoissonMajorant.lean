module

public import OddPiPowers.PolynomialValues.Analysis.PoissonComparison
public import OddPiPowers.PolynomialValues.Analysis.CircleApproximation
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Tactic.Linarith

/-! A continuous boundary majorant bounds every interior value.
An analytic zero at the origin contributes its full multiplicity. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Real Metric Filter Set Polynomial
open scoped Topology

theorem analytic_poisson_majorant {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 1))
    {b : ℂ → ℝ} (hb : ContinuousOn b (sphere 0 1))
    (hbound : ∀ z ∈ sphere 0 1, ‖f z‖ ≤ Real.exp (b z)) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖f w‖ ≤ Real.exp (poissonMean w b) := by
  by_cases hz : f w=0
  · simp [hz,le_of_lt (Real.exp_pos _)]
  have hpos := norm_pos_iff.mpr hz
  apply (Real.log_le_iff_le_exp hpos).mp
  by_contra! hbad
  let ε := (Real.log ‖f w‖-poissonMean w b)/3
  have he : 0 < ε := by dsimp [ε]; linarith
  let B : C(Circle,ℝ) := ⟨fun z => b (z : ℂ),hb.restrict⟩
  obtain ⟨p,hp⟩ := exists_polynomial_re_approx B he
  have hp' (z : ℂ) (hz : z ∈ sphere 0 1) :
      |(p.eval z).re-b z| < ε := hp ⟨z,hz⟩
  have hpA : AnalyticOnNhd ℂ (fun z => p.eval z) (closedBall 0 1) :=
    (AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)
  have hpR : ContinuousOn (fun z => (p.eval z).re) (sphere 0 1) :=
    Complex.continuous_re.comp_continuousOn (hpA.continuousOn.mono sphere_subset_closedBall)
  have hbε : poissonMean w (fun z => b z+ε) = poissonMean w b+ε := by
    rw [poissonMean_add hw hb continuousOn_const,poissonMean_const hw]
  have hpw := poissonMean_mono hw hpR (hb.add continuousOn_const)
    (g := fun z => b z+ε) (fun z hz => by linarith [(abs_lt.mp (hp' z hz)).2])
  rw [poissonMean_re hw hpA,hbε] at hpw
  let g (z : ℂ) := f z*Complex.exp (-(p.eval z))
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := fun z hz =>
    (hf z hz).mul (hpA z hz).neg.cexp'
  have hg (z : ℂ) (hz : z ∈ sphere 0 1) : ‖g z‖ ≤ Real.exp ε := by
    rw [show ‖g z‖=‖f z‖*Real.exp (-(p.eval z).re) by simp [g,norm_mul,Complex.norm_exp]]
    calc
      _ ≤ Real.exp (b z)*Real.exp (-(p.eval z).re) :=
        mul_le_mul_of_nonneg_right (hbound z hz) (Real.exp_pos _).le
      _ ≤ Real.exp ε := by
        rw [← Real.exp_add,Real.exp_le_exp]
        linarith [(abs_lt.mp (hp' z hz)).1]
  have hgw := analytic_unit_norm_bound hw hga hg
  simp only [g,norm_mul,Complex.norm_exp,Complex.neg_re,Real.exp_neg,← div_eq_mul_inv] at hgw
  have hew := (div_le_iff₀ (Real.exp_pos _)).mp hgw
  rw [← Real.exp_add,← Real.log_le_iff_le_exp hpos] at hew
  dsimp [ε] at hew hpw
  linarith

theorem factored_poisson_majorant {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 1))
    (hg : AnalyticAt ℂ g 0) (h : ℕ) (hfg : ∀ z, f z=z^h*g z)
    {b : ℂ → ℝ} (hb : ContinuousOn b (sphere 0 1))
    (hbound : ∀ z ∈ sphere 0 1, ‖f z‖ ≤ Real.exp (b z)) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖f w‖ ≤ ‖w‖^h*Real.exp (poissonMean w b) := by
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := by
    intro z hz
    by_cases h0 : z=0
    · simpa [h0] using hg
    apply ((hf z hz).div (analyticAt_id.pow h) (pow_ne_zero h h0)).congr
    filter_upwards [eventually_ne_nhds h0] with y hy
    change f y/y^h=g y
    rw [hfg, mul_div_cancel_left₀ _ (pow_ne_zero h hy)]
  have hnorm (z : ℂ) (hz : z ∈ sphere 0 1) : ‖g z‖ ≤ Real.exp (b z) := by
    have h1 : ‖z‖=1 := by simpa [mem_sphere,dist_eq_norm] using hz
    simpa [hfg,norm_mul,norm_pow,h1] using hbound z hz
  rw [hfg w,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left (analytic_poisson_majorant hga hb hnorm hw) (pow_nonneg (norm_nonneg _) _)

end PiPolynomialValues
