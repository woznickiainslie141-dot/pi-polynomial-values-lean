module

public import OddPiPowers.PolynomialValues.Analysis.PoissonComparison
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The boundary law at a real interior point is the image of the
Poisson-weighted angular interval. Its integral gives the same Poisson
mean on arbitrary measurable tests, including step functions. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Set Complex Real Metric Filter
open scoped ComplexConjugate

noncomputable def poissonAngleDensity (r θ : ℝ) : ℝ :=
  (2*π)⁻¹*unitPoisson (r : ℂ) (circleMap 0 1 θ)

noncomputable def poissonLaw (r : ℝ) : Measure ℂ :=
  Measure.map (circleMap 0 1) ((volume.restrict (Ioc (-π) π)).withDensity
    (fun θ => ENNReal.ofReal (poissonAngleDensity r θ)))

theorem circleAverage_symmetric_interval (f : ℂ → ℝ) :
    circleAverage f 0 1=(2*π)⁻¹*(∫ θ in -π..π, f (circleMap 0 1 θ)) := by
  rw [circleAverage_eq_integral_add (-π),smul_eq_mul,
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap 0 1 θ)),zero_add]
  ring_nf

theorem integral_poissonLaw {r : ℝ} (hr : ‖(r : ℂ)‖<1) {f : ℂ → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂poissonLaw r)=poissonMean (r : ℂ) f := by
  have hc : Measurable (circleMap 0 1) := (continuous_circleMap 0 1).measurable
  have hm : Measurable (poissonAngleDensity r) := by
    unfold poissonAngleDensity unitPoisson
    fun_prop
  have hn (θ : ℝ) : 0≤poissonAngleDensity r θ :=
    mul_nonneg (by positivity) (unitPoisson_nonneg hr.le _)
  rw [poissonLaw,integral_map hc.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal.aemeasurable
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),poissonMean,circleAverage_symmetric_interval,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π≤π),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  rw [ENNReal.toReal_ofReal (hn θ),smul_eq_mul,poissonAngleDensity,mul_assoc]

theorem poissonLaw_probability {r : ℝ} (hr : ‖(r : ℂ)‖<1) : IsProbabilityMeasure (poissonLaw r) := by
  have he := (integral_poissonLaw hr (f := fun _ => (1 : ℝ)) measurable_const).trans (poissonMean_const hr 1)
  rw [integral_const,smul_eq_mul,mul_one,measureReal_def] at he
  have ht : (poissonLaw r) univ ≠ ⊤ := by intro h; simp [h] at he
  constructor
  simpa only [ENNReal.ofReal_toReal ht,ENNReal.ofReal_one] using congrArg ENNReal.ofReal he

theorem poissonLaw_unit (r : ℝ) : ∀ᵐ z ∂poissonLaw r, ‖z‖=1 := by
  apply ae_map_iff (continuous_circleMap 0 1).measurable.aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const) |>.mpr
  exact Eventually.of_forall (by intro θ; simp)

theorem circleMap_conj_angle (θ : ℝ) : conj (circleMap 0 1 θ)=circleMap 0 1 (-θ) := by
  simp [circleMap,← Complex.exp_conj]

theorem poissonMean_conj_real (r : ℝ) (f : ℂ → ℝ) :
    poissonMean (r : ℂ) (fun z => f (conj z))=poissonMean (r : ℂ) f := by
  have he (θ : ℝ) : unitPoisson (r : ℂ) (circleMap 0 1 θ)=unitPoisson (r : ℂ) (circleMap 0 1 (-θ)) := by
    rw [← circleMap_conj_angle]
    have h : conj (circleMap 0 1 θ)-(r : ℂ)=conj (circleMap 0 1 θ-(r : ℂ)) := by simp
    simp only [unitPoisson,h,Complex.norm_conj]
  simp only [poissonMean,circleAverage_symmetric_interval,circleMap_conj_angle]
  conv_lhs => enter [2]; arg 1; ext θ; rw [he θ]
  rw [intervalIntegral.integral_comp_neg (fun θ => unitPoisson (r : ℂ) (circleMap 0 1 θ)*f (circleMap 0 1 θ)),neg_neg]

theorem poissonLaw_conj {r : ℝ} (hr : ‖(r : ℂ)‖<1) :
    MeasurePreserving (starRingEnd ℂ) (poissonLaw r) (poissonLaw r) := by
  letI := poissonLaw_probability hr
  have hc : Measurable (starRingEnd ℂ) := Complex.continuous_conj.measurable
  refine ⟨hc,?_⟩
  ext s hs
  rw [Measure.map_apply hc hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (poissonLaw r).real ((starRingEnd ℂ) ⁻¹' s)=(poissonLaw r).real s
  rw [← integral_indicator_one (hc hs),← integral_indicator_one hs]
  have hp (z : ℂ) : ((starRingEnd ℂ) ⁻¹' s).indicator (1 : ℂ → ℝ) z=s.indicator 1 (conj z) := by
    by_cases h : conj z∈s <;> simp [Set.indicator,Set.mem_preimage,h]
  simp_rw [hp]
  let F := s.indicator (1 : ℂ → ℝ)
  have hF : Measurable F := measurable_const.indicator hs
  exact (integral_poissonLaw hr (hF.comp hc)).trans ((poissonMean_conj_real r F).trans (integral_poissonLaw hr hF).symm)

end PiPolynomialValues
