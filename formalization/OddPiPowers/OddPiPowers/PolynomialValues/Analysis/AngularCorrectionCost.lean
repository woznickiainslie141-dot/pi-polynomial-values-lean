module

public import OddPiPowers.PolynomialValues.EvaluationPlan
public import OddPiPowers.PolynomialValues.Analysis.PathSlopeErrors

/-! Choose all analytic increments and their common endpoint correction
with the certified signed sine moment in the integrated cost. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter Real MeasureTheory Polynomial Metric Set
open scoped Topology

noncomputable def correctionMean (r t : ℝ) := ∫ w, |(correctionPath r t w).im| ∂poissonLaw r

theorem correction_integrable {r t : ℝ} (hr : ‖(r : ℂ)‖<1) (ht : 0≤t) (ht1 : t<1) :
    Integrable (fun w => |(correctionPath r t w).im|) (poissonLaw r) := by
  apply integrable_on_poisson_circle hr
  have h : ContinuousOn (correctionPath r t) (sphere (0 : ℂ) 1) :=
    ((analyticOnNhd_id.mul (correctionFactor_analytic ht ht1 r)).continuousOn).mono sphere_subset_closedBall
  exact (Complex.continuous_im.comp_continuousOn h).abs

theorem correctionMean_limit {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    Tendsto (fun j => correctionMean r (innerRadius j)) atTop (𝓝 (radiusMoment r)) := by
  have h := correction_mean_limit (fun j => (innerRadius_bounds j).1) (fun j => (innerRadius_bounds j).2)
    innerRadius_tendsto hr hr1
  apply h.congr
  intro j
  exact (integral_poissonLaw (by simpa [abs_of_pos hr] using hr1)
    (by unfold correctionPath correctionFactor; fun_prop : Measurable (fun w => |(correctionPath r (innerRadius j) w).im|))).symm

namespace EvaluationPlan

noncomputable def sineCost (P : EvaluationPlan) := π*(radiusCutQ P.rates : ℝ)*(P.rates.moment : ℝ)+
  (P.design.sineForm (upperNodeMoments P.shape P.cuts) P.rates.length).actual P.rates.radius true

noncomputable def angularCost (P : EvaluationPlan) := (P.rates.baseCost : ℝ)+
  P.design.energyForm.actual P.rates.radius false+P.sineCost

theorem correction_identity (P : EvaluationPlan) :
    (∑ k : Fin P.cuts.length, (cutWeight P.shape P.cuts P.rates k : ℝ)*
      (π/2*radiusMoment P.rates.radius-(P.design.directionForm k.val).actual P.rates.radius true))=P.sineCost := by
  rw [P.design.direction_moments P.shape P.cuts P.rates P.arcs P.valid P.moments]
  unfold sineCost radiusMoment radiusCutQ
  push_cast
  ring

theorem correction_choice (P : EvaluationPlan) {ε : ℝ} (hε : 0<ε) :
    let r := (P.rates.radius : ℝ)
    let L := (P.rates.length : ℝ)
    let F (j : Fin P.cuts.length) := P.design.directionForm j.val
    ∃ (g : Fin P.cuts.length → ℂ[X]) (t : ℝ), 0<t ∧ t<1 ∧
      (∀ j, (g j).eval 0=0 ∧ (∀ x : ℝ, ((g j).eval (x : ℂ)).im=0) ∧ 0<pathGap r (g j)) ∧
      L*(∫ w, slopeError g F w ∂poissonLaw r)+correctionMean r t*
        (∑ j, pathGap r (g j)*(2*(cutMomentQ P.shape (P.cuts.get j) : ℝ)))≤L*P.sineCost+ε := by
  intro r L F
  let ρ := radiusMoment r
  let w (j : Fin P.cuts.length) := (cutWeight P.shape P.cuts P.rates j : ℝ)
  let d := ∑ j, |w j|
  let C := L*((P.cuts.length : ℝ)+d)
  have hC : 0≤C := mul_nonneg P.length_pos.le (add_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => abs_nonneg _)))
  let η := ε/(2*(C+1))
  have hη : 0<η := by dsimp only [η]; positivity
  choose g h₀ hreal he hM hgap using fun j : Fin P.cuts.length =>
    positive_increment_path P.radius_bounds.1 P.radius_bounds.2 (F j) (P.direction_margin j) hη
  let S := ∑ j, pathGap r (g j)*(2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))
  have hE := slopeError_integral (by simpa [abs_of_pos P.radius_bounds.1] using P.radius_bounds.2) g F η he
  have hpoint (j : Fin P.cuts.length) :
      w j*(ρ*pathGap r (g j))≤w j*(π/2*ρ-(F j).actual P.rates.radius true)+|w j| * η := by
    have h := mul_le_mul_of_nonneg_left (hM j) (abs_nonneg (w j))
    rw [← abs_mul] at h
    have h' := (neg_le_neg h).trans (neg_abs_le _)
    dsimp only [pathGap,ρ]
    dsimp only [r,F] at *
    nlinarith only [h']
  have hsum := sum_le_sum (s := univ) (fun j _ => hpoint j)
  rw [sum_add_distrib,← sum_mul] at hsum
  have hcost : (∑ j, w j*(π/2*ρ-(F j).actual P.rates.radius true))=P.sineCost := P.correction_identity
  rw [hcost] at hsum
  have hweight (j : Fin P.cuts.length) : 2*(cutMomentQ P.shape (P.cuts.get j) : ℝ)=L*w j := by
    simp only [w,cutWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,L]
    field_simp [P.length_pos.ne']
  have hS : ρ*S=L*(∑ j, w j*(ρ*pathGap r (g j))) := by
    simp only [S,hweight,mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  have hlim := (correctionMean_limit P.radius_bounds.1 P.radius_bounds.2).mul_const S
  obtain ⟨j,hj⟩ := (hlim.eventually (gt_mem_nhds (show ρ*S<ρ*S+ε/2 by linarith))).exists
  have hηeq : 2*(C+1)*η=ε := by dsimp only [η]; field_simp
  have hL := mul_le_mul_of_nonneg_left hsum P.length_pos.le
  have heL := mul_le_mul_of_nonneg_left hE P.length_pos.le
  refine ⟨g,innerRadius j,(innerRadius_bounds j).1,(innerRadius_bounds j).2,fun j => ⟨h₀ j,hreal j,hgap j⟩,?_⟩
  change L*_+correctionMean r (innerRadius j)*S≤_
  dsimp only [C] at hηeq
  nlinarith only [hS,hj.le,hL,heL,hηeq,hη.le]

end EvaluationPlan
end PiPolynomialValues
