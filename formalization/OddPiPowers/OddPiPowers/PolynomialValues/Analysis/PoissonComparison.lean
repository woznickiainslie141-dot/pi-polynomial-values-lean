module

public import OddPiPowers.PolynomialValues.Analysis.UnitPoisson
import Mathlib.Tactic.Positivity

/-! Monotonicity and analytic comparison for weighted unit-circle means. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Real Metric Set

noncomputable def poissonMean (w : ℂ) (f : ℂ → ℝ) : ℝ :=
  circleAverage (fun z => unitPoisson w z*f z) 0 1

theorem poissonMean_re {w : ℂ} (hw : ‖w‖ < 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    poissonMean w (fun z => (f z).re) = (f w).re := by
  let F (z : ℂ) := (unitPoisson w z : ℂ)*f z
  have hF : ContinuousOn F (sphere 0 1) :=
    (Complex.continuous_ofReal.comp_continuousOn (unitPoisson_continuousOn hw)).mul
      (hf.continuousOn.mono sphere_subset_closedBall)
  have he := Complex.reCLM.circleAverage_comp_comm (hF.circleIntegrable zero_le_one)
  rw [show circleAverage F 0 1 = f w from unitPoisson_mean hw hf] at he
  simpa [F,poissonMean,Function.comp_def] using he

theorem poissonMean_const {w : ℂ} (hw : ‖w‖ < 1) (M : ℝ) :
    poissonMean w (fun _ => M) = M := by
  exact poissonMean_re hw (f := fun _ => (M : ℂ)) analyticOnNhd_const

theorem poissonMean_mono {w : ℂ} (hw : ‖w‖ < 1) {f g : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) (hg : ContinuousOn g (sphere 0 1))
    (h : ∀ z ∈ sphere 0 1, f z ≤ g z) : poissonMean w f ≤ poissonMean w g := by
  apply Real.circleAverage_mono (((unitPoisson_continuousOn hw).mul hf).circleIntegrable zero_le_one)
    (((unitPoisson_continuousOn hw).mul hg).circleIntegrable zero_le_one)
  intro z hz
  exact mul_le_mul_of_nonneg_left (h z (by simpa using hz)) (unitPoisson_nonneg hw.le z)

theorem poissonMean_add {w : ℂ} (hw : ‖w‖ < 1) {f g : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) (hg : ContinuousOn g (sphere 0 1)) :
    poissonMean w (fun z => f z+g z) = poissonMean w f+poissonMean w g := by
  unfold poissonMean
  simp_rw [mul_add]
  exact circleAverage_add (((unitPoisson_continuousOn hw).mul hf).circleIntegrable zero_le_one)
    (((unitPoisson_continuousOn hw).mul hg).circleIntegrable zero_le_one)

theorem norm_le_poissonMean {w : ℂ} (hw : ‖w‖ < 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) : ‖f w‖ ≤ poissonMean w (fun z => ‖f z‖) := by
  rw [← unitPoisson_mean hw hf]
  apply Real.norm_circleAverage_le_circleAverage_norm.trans (le_of_eq ?_)
  apply circleAverage_congr_sphere
  intro z _
  simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (unitPoisson_nonneg hw.le z)]

theorem analytic_unit_norm_bound {w : ℂ} (hw : ‖w‖ < 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) {M : ℝ}
    (hM : ∀ z ∈ sphere 0 1, ‖f z‖ ≤ M) : ‖f w‖ ≤ M :=
  (norm_le_poissonMean hw hf).trans ((poissonMean_mono hw
    (hf.continuousOn.mono sphere_subset_closedBall).norm continuousOn_const hM).trans_eq
      (poissonMean_const hw M))

end PiPolynomialValues
