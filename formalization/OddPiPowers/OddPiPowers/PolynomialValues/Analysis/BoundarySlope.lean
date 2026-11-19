module

public import OddPiPowers.PolynomialValues.Analysis.PoissonLaw
public import OddPiPowers.PolynomialValues.Analysis.BoundaryFieldApproximation
public import OddPiPowers.PolynomialValues.Analysis.CorrectedMoment

/-! Approximation in the actual Poisson probability controls both the
boundary field and the interior value of the polynomial path. -/

@[expose] public section

namespace PiPolynomialValues

open Real Complex Polynomial MeasureTheory Metric Filter Set
open scoped ComplexConjugate

theorem integrable_on_poisson_circle {r : ℝ} (hr : ‖(r : ℂ)‖<1) {f : ℂ → ℝ}
    (h : ContinuousOn f (sphere 0 1)) : Integrable f (poissonLaw r) := by
  letI := poissonLaw_probability hr
  have hmem : ∀ᵐ w ∂poissonLaw r, w∈sphere (0 : ℂ) 1 := (poissonLaw_unit r).mono
    (fun w hw => mem_sphere_zero_iff_norm.mpr hw)
  have H := h.integrableOn_compact (μ := poissonLaw r) (isCompact_sphere (0 : ℂ) 1)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hmem] at H

theorem poisson_moment_lipschitz {r : ℝ} {f b : ℂ → ℝ} (hf : Integrable f (poissonLaw r))
    (hb : Integrable b (poissonLaw r)) :
    |(∫ w : ℂ, f w*w.im ∂poissonLaw r)-(∫ w : ℂ, b w*w.im ∂poissonLaw r)|≤
      ∫ w, |f w-b w| ∂poissonLaw r := by
  have H : ∀ᵐ w ∂poissonLaw r, ‖w.im‖≤1 := (poissonLaw_unit r).mono
    (fun w hw => (Complex.abs_im_le_norm w).trans_eq hw)
  have hm := Complex.continuous_im.aestronglyMeasurable (μ := poissonLaw r)
  rw [← integral_sub (hf.mul_bdd hm H) (hb.mul_bdd hm H)]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _)) (hf.sub hb).norm
  filter_upwards [H] with w hw
  rw [← sub_mul,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hw

theorem exists_boundary_slope {r : ℝ} (hr : 0<r) (hr1 : r<1) {b : ℂ → ℝ}
    (hb : Integrable b (poissonLaw r)) (ho : ∀ᵐ w ∂poissonLaw r, b (conj w) = -b w)
    {ε : ℝ} (hε : 0<ε) :
    ∃ g : ℂ[X], g.eval 0=0 ∧ (∀ x : ℝ, (g.eval (x : ℂ)).im=0) ∧
      (∫ w, |(g.eval w).im-b w| ∂poissonLaw r)≤ε ∧
      |(r⁻¹-r)*(g.eval (r : ℂ)).re/2-(∫ w : ℂ, b w*w.im ∂poissonLaw r)|≤ε := by
  have hw : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr] using hr1
  letI := poissonLaw_probability hw
  obtain ⟨g,h0,hreal,hclose⟩ := integrable_boundary_path (poissonLaw_unit r) (poissonLaw_conj hw) hb ho hε
  have hc : Continuous (fun w : ℂ => (g.eval w).im) := Complex.continuous_im.comp g.continuous
  have he := (integral_poissonLaw hw (hc.mul Complex.continuous_im).measurable).trans
    (polynomial_sine_moment g h0 hr hr1)
  refine ⟨g,h0,hreal,hclose,?_⟩
  rw [← he]
  exact (poisson_moment_lipschitz (integrable_on_poisson_circle hw hc.continuousOn) hb).trans hclose

end PiPolynomialValues
