module

public import OddPiPowers.PolynomialValues.Analysis.ArcGate

/-! The two semicircles carry equal weight for every folded test.
The prescribed signed direction is odd and its first sine moment is
the folded moment with positive ordinate. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Real MeasureTheory Set Filter
open scoped ComplexConjugate

noncomputable def lowerFace (w : ℂ) : ℝ := if w.im<0 then 1 else if 0<w.im then 0 else 1/2
noncomputable def boundarySign (w : ℂ) : ℝ := if w.im<0 then -1 else if 0<w.im then 1 else 0

theorem lowerFace_measurable : Measurable lowerFace :=
  measurable_const.piecewise (measurableSet_lt Complex.continuous_im.measurable measurable_const)
    (measurable_const.piecewise (measurableSet_lt measurable_const Complex.continuous_im.measurable) measurable_const)

theorem boundarySign_measurable : Measurable boundarySign :=
  measurable_const.piecewise (measurableSet_lt Complex.continuous_im.measurable measurable_const)
    (measurable_const.piecewise (measurableSet_lt measurable_const Complex.continuous_im.measurable) measurable_const)

theorem foldedAngle_conj (w : ℂ) : foldedAngle (conj w)=foldedAngle w := by simp [foldedAngle]

theorem lowerFace_abs_le (w : ℂ) : |lowerFace w|≤1 := by unfold lowerFace; split_ifs <;> norm_num

theorem lowerFace_conj (w : ℂ) : lowerFace w+lowerFace (conj w)=1 := by
  unfold lowerFace
  rw [Complex.conj_im]
  split_ifs <;> linarith

theorem boundarySign_conj (w : ℂ) : boundarySign (conj w) = -boundarySign w := by
  unfold boundarySign
  rw [Complex.conj_im]
  split_ifs <;> linarith

theorem boundarySign_mul_im (w : ℂ) : boundarySign w*w.im=|w.im| := by
  rcases lt_trichotomy w.im 0 with h|h|h
  · simp [boundarySign,h,abs_of_neg h]
  · simp [boundarySign,h]
  · simp [boundarySign,h,h.not_gt,abs_of_pos h]

theorem half_fold_integral {r : ℝ} (hr : ‖(r : ℂ)‖<1) (f : ℝ → ℝ)
    (hf : Integrable (fun w => f (foldedAngle w)) (poissonLaw r)) :
    (∫ w, lowerFace w*f (foldedAngle w) ∂poissonLaw r)=
      (∫ w, f (foldedAngle w) ∂poissonLaw r)/2 := by
  let F (w : ℂ) := lowerFace w*f (foldedAngle w)
  have hi : Integrable F (poissonLaw r) := hf.bdd_mul lowerFace_measurable.aestronglyMeasurable
    (Eventually.of_forall (fun w => lowerFace_abs_le w))
  have hc := poissonLaw_conj hr
  have hi' := hc.integrable_comp_of_integrable hi
  have he := hc.integral_comp Complex.conjCLE.toHomeomorph.measurableEmbedding F
  change (∫ w, F (conj w) ∂poissonLaw r)=∫ w, F w ∂poissonLaw r at he
  have hadd : (∫ w, F w ∂poissonLaw r)+(∫ w, F (conj w) ∂poissonLaw r)=
      ∫ w, f (foldedAngle w) ∂poissonLaw r := by
    rw [← integral_add (f := F) (g := fun z => F (conj z)) hi hi']
    apply integral_congr_ae
    apply Eventually.of_forall
    intro w
    change lowerFace w*f (foldedAngle w)+lowerFace (conj w)*f (foldedAngle (conj w))=_
    rw [foldedAngle_conj,← add_mul,lowerFace_conj,one_mul]
  rw [he] at hadd
  change (∫ w, F w ∂poissonLaw r)=_
  linarith only [hadd]

noncomputable def signedFold (f : ℝ → ℝ) (w : ℂ) := boundarySign w*f (foldedAngle w)

theorem signedFold_odd (f : ℝ → ℝ) (w : ℂ) : signedFold f (conj w) = -signedFold f w := by
  rw [signedFold,signedFold,boundarySign_conj,foldedAngle_conj,neg_mul]

theorem signedFold_moment (f : ℝ → ℝ) (w : ℂ) : signedFold f w*w.im=f (foldedAngle w)*|w.im| := by
  rw [signedFold,← boundarySign_mul_im w]
  ring

theorem foldedTest_integrable {r : ℝ} (hr : ‖(r : ℂ)‖<1) {f : ℝ → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ θ∈Icc 0 (π/2), |f θ|≤B) :
    Integrable (fun w => f (foldedAngle w)) (poissonLaw r) := by
  letI := poissonLaw_probability hr
  exact (integrable_const B).mono' (hf.comp foldedAngle_continuous.measurable).aestronglyMeasurable
    (Eventually.of_forall (fun w => hB _ (foldedAngle_mem w)))

theorem signedFold_integrable {r : ℝ} (hr : ‖(r : ℂ)‖<1) {f : ℝ → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ θ∈Icc 0 (π/2), |f θ|≤B) : Integrable (signedFold f) (poissonLaw r) := by
  apply (foldedTest_integrable hr hf hB).bdd_mul boundarySign_measurable.aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  change |boundarySign w|≤(1 : ℝ)
  unfold boundarySign
  split_ifs <;> norm_num

end PiPolynomialValues
