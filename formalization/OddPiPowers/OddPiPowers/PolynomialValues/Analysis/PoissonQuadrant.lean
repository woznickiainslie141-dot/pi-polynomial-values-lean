module

public import OddPiPowers.PolynomialValues.Analysis.PoissonLaw
public import OddPiPowers.PolynomialValues.Analysis.FoldedPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Folding the actual real-radius Poisson law onto its first quadrant
gives the density used by the angular interval certificates. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Set Real Complex Filter

noncomputable def foldedAngle (z : ℂ) := Real.arcsin |z.im|
noncomputable def angleKernel (r θ : ℝ) := (1-r^2)/(1+r^2-2*r*Real.cos θ)

theorem foldedAngle_continuous : Continuous foldedAngle :=
  Real.continuous_arcsin.comp Complex.continuous_im.abs

theorem foldedAngle_mem (z : ℂ) : foldedAngle z ∈ Icc 0 (π/2) :=
  ⟨Real.arcsin_nonneg.mpr (abs_nonneg _),Real.arcsin_le_pi_div_two _⟩

theorem unitCircle_coordinates (θ : ℝ) : (circleMap 0 1 θ).re=Real.cos θ ∧
    (circleMap 0 1 θ).im=Real.sin θ := by
  simp [circleMap,Complex.exp_mul_I,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

theorem unitPoisson_angle (r θ : ℝ) : unitPoisson (r : ℂ) (circleMap 0 1 θ)=angleKernel r θ := by
  have hh := unitCircle_coordinates θ
  have h : ‖circleMap 0 1 θ-(r : ℂ)‖^2=1+r^2-2*r*Real.cos θ := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,hh.1,hh.2]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp [unitPoisson,angleKernel,h,sq_abs]

theorem angleKernel_den_pos {r : ℝ} (hr : 0<r) (hr1 : r<1) (θ : ℝ) :
    0<1+r^2-2*r*Real.cos θ := by
  nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hr.le,sq_pos_of_pos (sub_pos.mpr hr1)]

theorem quadrant_density_identity {r : ℝ} (hr : 0<r) (hr1 : r<1) (θ : ℝ) :
    (angleKernel r θ+angleKernel r (π-θ))/π=foldedPoisson r θ := by
  have h1 := angleKernel_den_pos hr hr1 θ
  have h2 := angleKernel_den_pos hr hr1 (π-θ)
  rw [Real.cos_pi_sub] at h2
  have he : (1+r^2-2*r*Real.cos θ)*(1+r^2-2*r*(-Real.cos θ))=(1-r^2)^2+4*r^2*Real.sin θ^2 := by
    linear_combination -4*r^2*(Real.sin_sq_add_cos_sq θ)
  unfold angleKernel foldedPoisson
  rw [Real.cos_pi_sub,← he]
  let A := 1+r^2-2*r*Real.cos θ
  let B := 1+r^2-2*r*(-Real.cos θ)
  have hA : A≠0 := h1.ne'
  have hB : B≠0 := h2.ne'
  change ((1-r^2)/A+(1-r^2)/B)/π=(2/π)*((1-r^4)/(A*B))
  field_simp [hA,hB,Real.pi_ne_zero]
  dsimp only [A,B]
  ring

theorem poissonLaw_fold {r : ℝ} (hr : 0<r) (hr1 : r<1) {f : ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x ∈ Icc 0 (π/2), |f x|≤M) :
    (∫ z, f (foldedAngle z) ∂poissonLaw r) = ∫ θ in 0..π/2, foldedPoisson r θ*f θ := by
  have hw : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr] using hr1
  let F (θ : ℝ) := angleKernel r θ*f (foldedAngle (circleMap 0 1 θ))
  have ha : Continuous (angleKernel r) := continuous_const.div₀ (by fun_prop)
    (fun θ => (angleKernel_den_pos hr hr1 θ).ne')
  have hF (a b : ℝ) : IntervalIntegrable F volume a b := by
    have hI : IntervalIntegrable (fun t => |angleKernel r t| * M) volume a b :=
      (ha.abs.mul continuous_const).intervalIntegrable a b
    apply hI.mono_fun' (f := F) (ha.measurable.mul
      (hf.comp (foldedAngle_continuous.comp (continuous_circleMap 0 1)).measurable)).aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    simp only [F,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _ (foldedAngle_mem _)) (abs_nonneg _)
  have heven (t : ℝ) : F (-t)=F t := by
    simp [F,angleKernel,foldedAngle,(unitCircle_coordinates _).2]
  have hright (t : ℝ) (ht : t∈Icc 0 (π/2)) : foldedAngle (circleMap 0 1 t)=t := by
    rw [foldedAngle,(unitCircle_coordinates _).2,abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (ht.2.trans (by linarith [Real.pi_pos]))),Real.arcsin_sin (by linarith [ht.1,Real.pi_pos]) ht.2]
  have hreflect (t : ℝ) : foldedAngle (circleMap 0 1 (π-t))=foldedAngle (circleMap 0 1 t) := by
    simp only [foldedAngle,(unitCircle_coordinates _).2,Real.sin_pi_sub]
  have hl : (∫ t in -π..0, F t)=∫ t in 0..π, F t := by
    simpa only [heven,neg_zero,neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -π) (b := 0) F)
  have htop : (∫ t in π/2..π, F t)=∫ t in 0..π/2, F (π-t) := by
    rw [intervalIntegral.integral_comp_sub_left F π]
    congr 1 <;> ring
  have hRI : IntervalIntegrable (fun t => F (π-t)) volume 0 (π/2) := by
    simpa only [sub_self,show π-π/2=π/2 by ring] using (hF π (π/2)).comp_sub_left π
  rw [integral_poissonLaw (f := fun z => f (foldedAngle z)) hw (hf.comp foldedAngle_continuous.measurable),
    poissonMean,circleAverage_symmetric_interval]
  simp_rw [unitPoisson_angle]
  change (2*π)⁻¹*(∫ t in -π..π, F t)=_
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF (-π) 0) (hF 0 π),hl,
    ← intervalIntegral.integral_add_adjacent_intervals (hF 0 (π/2)) (hF (π/2) π),htop,
    ← intervalIntegral.integral_add (hF 0 (π/2)) hRI,← two_mul,← mul_assoc,
    show (2*π)⁻¹*2=π⁻¹ by field_simp,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by positivity)] at ht
  dsimp only [F]
  rw [hreflect,hright t ht,← quadrant_density_identity hr hr1]
  ring

end PiPolynomialValues
