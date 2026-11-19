module

public import OddPiPowers.PolynomialValues.Analysis.CenteredPathEstimate
public import OddPiPowers.PolynomialValues.Analysis.BoundarySlope

/-! Measurable, integrable numerical majorants can be discontinuous at
the angular cuts. A continuous truncated logarithm of the determinant
transfers their integral to the original interior evaluation. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open MeasureTheory Metric Set Complex Filter

theorem centered_path_integral {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ → ℂ) (hp : ∀ i, AnalyticOnNhd ℂ (p i) (closedBall 0 1)) (h0 : ∀ i, p i 0=0)
    {r : ℝ} (hr : ‖(r : ℂ)‖<1) {b : ℂ → ℝ} (hb : Integrable b (poissonLaw r)) {L : ℝ}
    (hL : ∀ᵐ z ∂poissonLaw r, L≤b z)
    (hbound : ∀ᵐ z ∂poissonLaw r, ‖(centeredLabelMatrix e v x j a h (fun i => p i z)).det‖≤Real.exp (b z)) :
    ∃ q : LabelChoice (fun c => (h c).val),
      ‖(centeredLabelMatrix e v x j a h (fun i => p i (r : ℂ))).det‖≤
        ‖(r : ℂ)‖^(labelPairs (fun c => (q c).val)-∑ i, (e i).2.val)*Real.exp (∫ z, b z ∂poissonLaw r) := by
  classical
  let f (z : ℂ) := (centeredLabelMatrix e v x j a h (fun i => p i z)).det
  let S := sphere (0:ℂ) 1
  let A (z : ℂ) := Real.log (max (Real.exp L) ‖f z‖)
  let B := S.piecewise A (fun _ => 0)
  have hpos (z : ℂ) : 0<max (Real.exp L) ‖f z‖ := (Real.exp_pos L).trans_le (le_max_left _ _)
  have hS : MeasurableSet S := isClosed_sphere.measurableSet
  have hf : ContinuousOn f S := fun z hz => (centered_det_analytic e v x j a h p
    (fun i => hp i z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hmax : ContinuousOn (fun z => max (Real.exp L) ‖f z‖) S := by fun_prop
  have hA : ContinuousOn A S := hmax.log (fun z _ => (hpos z).ne')
  have hEq (z : ℂ) (hz : z∈S) : B z=A z := S.piecewise_eq_of_mem _ _ hz
  have hB : ContinuousOn B S := hA.congr hEq
  have hmeas : Measurable B := hA.measurable_piecewise continuousOn_const hS
  have hBbound (z : ℂ) (hz : z∈S) : ‖f z‖≤Real.exp (B z) := by
    rw [hEq z hz,show Real.exp (A z)=_ from Real.exp_log (hpos z)]
    exact le_max_right _ _
  obtain ⟨q,hq⟩ := centered_path_poisson e v x j a h p hp h0 hB hBbound hr
  have he : poissonMean (r : ℂ) B≤∫ w, b w ∂poissonLaw r := by
    rw [← integral_poissonLaw hr hmeas]
    apply integral_mono_ae (integrable_on_poisson_circle hr hB) hb
    filter_upwards [poissonLaw_unit r,hL,hbound] with z hz hl hd
    rw [hEq z (mem_sphere_zero_iff_norm.mpr hz)]
    exact (Real.log_le_log (hpos z) (max_le (Real.exp_le_exp.mpr hl) hd)).trans_eq (Real.log_exp _)
  refine ⟨q,hq.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))⟩

end PiPolynomialValues.FourPeriod
