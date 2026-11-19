module

public import OddPiPowers.PolynomialValues.Analysis.BoundaryAllocation
public import OddPiPowers.PolynomialValues.Analysis.PathSlopeErrors

/-! Integrate the two spatial charges on their actual semicircles, including
the price paid only on the lower semicircle by a positive Taylor label. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Filter Real

noncomputable def AngleDesign.faceEnergy (D : AngleDesign) (w : ℂ) :=
  let O := (D.form AngleLabel.ordinary).field (foldedAngle w)
  let T := (D.form AngleLabel.tilted).field (foldedAngle w)
  O+lowerFace w*(T-O)

noncomputable def AngleDesign.faceFee (D : AngleDesign) (w : ℂ) :=
  lowerFace w*(2*D.priceForm.field (foldedAngle w))

theorem AngleDesign.faceEnergy_at (D : AngleDesign) (w : ℂ) (h : w.im≠0) :
    D.faceEnergy w=D.weightAt (foldedAngle w) (fun t => if upperSide w then (t.ordinary : ℝ) else (t.tilted : ℝ)) := by
  rcases lt_or_gt_of_ne h with h|h
  · simp only [faceEnergy,lowerFace,if_pos h,upperSide,decide_eq_false h.not_gt,Bool.false_eq_true,if_false,one_mul]
    rw [D.weightAt_form AngleLabel.tilted]
    ring
  · simp only [faceEnergy,lowerFace,if_neg h.not_gt,if_pos h,upperSide,decide_eq_true h,if_true,zero_mul,add_zero]
    exact (D.weightAt_form AngleLabel.ordinary _).symm

theorem AngleDesign.faceFee_at (D : AngleDesign) (s : FourPeriod.Shape) (arcs : List ArcRow) (hd : D.valid s arcs=true)
    (w : ℂ) (h : w.im≠0) (hθ : D.weightAt (foldedAngle w) (fun _ => 1)=1) :
    D.faceFee w=D.weightAt (foldedAngle w) (fun t => if upperSide w then 0 else (t.price : ℝ)/10^7) := by
  rcases lt_or_gt_of_ne h with h|h
  · simp only [faceFee,lowerFace,if_pos h,upperSide,decide_eq_false h.not_gt,Bool.false_eq_true,if_false,one_mul]
    calc
      2*D.priceForm.field (foldedAngle w)=D.weightAt (foldedAngle w) (fun t => 2*(((t.price : ℚ)/(2*10^7) : ℚ) : ℝ)) := by
        rw [D.weightAt_mul,D.weightAt_form]; rfl
      _ = _ := D.weightAt_congr s arcs hd _ (fun t _ => by push_cast; ring)
  · simp only [faceFee,lowerFace,if_neg h.not_gt,if_pos h,upperSide,decide_eq_true h,if_true,zero_mul]
    exact (D.weightAt_const _ 0 hθ).symm

theorem AngleDesign.face_integrals (D : AngleDesign) (z : ℚ) (hz : ‖((z : ℝ) : ℂ)‖<1) :
    Integrable D.faceEnergy (poissonLaw z) ∧ Integrable D.faceFee (poissonLaw z) ∧
      (∫ w, D.faceEnergy w ∂poissonLaw z)=D.energyForm.actual z false ∧
      (∫ w, D.faceFee w ∂poissonLaw z)=D.priceForm.actual z false := by
  let O := (D.form AngleLabel.ordinary).field
  let T := (D.form AngleLabel.tilted).field
  let P := D.priceForm.field
  have hi (f : ArcForm) := foldedTest_integrable hz f.field_measurable (fun θ _ => f.field_abs θ)
  have hO := hi (D.form AngleLabel.ordinary)
  have hT := hi (D.form AngleLabel.tilted)
  have hP := hi D.priceForm
  have hD : Integrable (fun w => T (foldedAngle w)-O (foldedAngle w)) (poissonLaw z) := hT.sub hO
  have hprice : Integrable (fun w => 2*P (foldedAngle w)) (poissonLaw z) := hP.const_mul 2
  have hL {f : ℂ → ℝ} (hf : Integrable f (poissonLaw z)) :
      Integrable (fun w => lowerFace w*f w) (poissonLaw z) :=
    hf.bdd_mul lowerFace_measurable.aestronglyMeasurable (Eventually.of_forall lowerFace_abs_le)
  refine ⟨hO.add (hL hD),hL hprice,?_,?_⟩
  · change (∫ w, O (foldedAngle w)+lowerFace w*(T (foldedAngle w)-O (foldedAngle w)) ∂poissonLaw z)=_
    rw [integral_add hO (hL hD),half_fold_integral hz (fun θ => T θ-O θ) hD,integral_sub hT hO]
    rw [← (D.energyForm.integral_field z hz).1]
    have H (θ : ℝ) : D.energyForm.field θ=(O θ+T θ)/2 := by
      have he := D.weightAt_mul θ (1/2) (fun t => (t.ordinary : ℝ)+(t.tilted : ℝ))
      rw [D.weightAt_add,D.weightAt_form AngleLabel.ordinary,D.weightAt_form AngleLabel.tilted] at he
      have hh : D.energyForm.field θ=D.weightAt θ (fun t => (1/2)*((t.ordinary : ℝ)+(t.tilted : ℝ))) := by
        rw [AngleDesign.energyForm,← D.weightAt_form AngleLabel.meanEnergy]
        congr 1
        funext t
        simp only [AngleLabel.meanEnergy,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat]
        ring
      rw [hh,he]; dsimp only [O,T]; ring
    simp only [H]
    rw [integral_div,integral_add hO hT]
    ring
  · change (∫ w, lowerFace w*(2*P (foldedAngle w)) ∂poissonLaw z)=_
    rw [half_fold_integral hz (fun θ => 2*P θ) hprice,integral_const_mul]
    change 2*(∫ w, D.priceForm.field (foldedAngle w) ∂poissonLaw z)/2=_
    rw [(D.priceForm.integral_field z hz).1]
    ring

end PiPolynomialValues
