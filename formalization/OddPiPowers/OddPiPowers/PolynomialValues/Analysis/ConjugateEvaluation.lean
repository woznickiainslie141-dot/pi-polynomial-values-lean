module

public import OddPiPowers.PolynomialValues.Analysis.PricedEvaluation
public import OddPiPowers.PolynomialValues.Analysis.ScalarMinorRate

/-! The principal-root estimate uses the designed paths. Each other
positive exponent chooses its own scalar radius, with a uniform slope
on the full interval of secondary exponents. -/

@[expose] public section

namespace PiPolynomialValues.EvaluationScale

open FourPeriod Finset Filter Real
open scoped Topology

variable {P : EvaluationPlan} {W : SelectedSequence P} (S : EvaluationScale W)

theorem principal_rate {z : ℕ → ℂ} (hne : ∀ i, (π : ℂ)≠z i)
    (hv : ∀ᶠ i in atTop, 0<reducedEvaluation (W.witness i).integral (z i)) {C b y : ℝ}
    (hroot : Tendsto (fun i => cappedProximity C (S.X i) π (z i)) atTop (𝓝 b))
    (hy : y≤(P.rates.Y : ℝ)) (hb : (P.rates.target : ℝ)-y≤b) :
    UpperRate atTop (S.normRate (fun i => log (reducedEvaluation (W.witness i).integral (z i))))
      ((P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+P.angularCost+
        (P.rates.rowSquare : ℝ)*log (1/(P.rates.radius : ℝ)))-
        pricedMinimum P.rates.B ((P.rates.target : ℝ)-y) P.rates.δ) := by
  obtain ⟨_,_,_,_,_,_,_,hB,hδ,ht,_,hh,_⟩ := P.tests
  have hT := (Rat.cast_pos (K := ℝ)).mpr ht
  have hH := (Rat.cast_lt (K := ℝ)).mpr hh
  push_cast at hT hH
  have hfee : (P.rates.δ : ℝ)=(P.rates.labelPrice : ℝ)*P.rates.scale := by
    simp [RateData.δ,mul_comm]
  have hpen := mul_le_mul_of_nonneg_left (P.shape.basePass_sound P.rates P.base).2.1 P.degree_scale_pos.le
  apply S.priced_rate hne hv hroot (by linarith only [hT,hy]) hb
    (by exact_mod_cast hB) (by exact_mod_cast hδ) (by linarith only [hH,hy]) hfee.le _
    P.radius_bounds.1 P.radius_bounds.2.le W.primary_minor_rate
  change ((P.rates.scale*P.rates.penalty : ℚ) : ℝ)≤_
  rw [Rat.cast_mul]
  exact hpen.trans_eq (by ring)

theorem scalar_radius {c : ℝ} (hc : 0<c) (hY : c≤(P.rates.Y : ℝ)) :
    let x := c/((P.rates.scale : ℝ)*P.rates.length)
    let r := exp (-x)
    0<r ∧ r<1 ∧ log (1/r)=x ∧
    (P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+P.scalarCost r+(P.rates.rowSquare : ℝ)*x)-c/2≤
      (P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+P.rates.baseCost+P.rates.ordinary)-(P.rates.secondaryLower : ℝ)*c := by
  intro x r
  obtain ⟨_,_,_,_,hm,hh,h1,_⟩ := P.tests
  have hm' : 0<(P.rates.moment : ℝ) := by exact_mod_cast hm
  have hh' : 0<(P.rates.hStar : ℝ) := by exact_mod_cast hh
  have h1' : (P.rates.hStar : ℝ)<1 := by exact_mod_cast h1
  have hbase := mul_pos P.degree_scale_pos P.length_pos
  have hx : 0<x := div_pos hc hbase
  have he : 1/r=exp x := by simp only [r,one_div,exp_neg,inv_inv]
  have hr1 : r<1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  refine ⟨exp_pos _,hr1,by rw [he,log_exp],?_⟩
  have htr : x≤(P.rates.hStar : ℝ) := by
    unfold RateData.hStar
    push_cast
    exact div_le_div_of_nonneg_right hY hbase.le
  have hs := scalar_sinh_rate hh'.le h1' hx.le htr
  have hs' : 0≤sinh x := by
    rw [Real.sinh_eq]
    exact div_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (by linarith))) (by norm_num)
  have hmoment : radiusMoment r=sinh x := by
    unfold radiusMoment
    rw [← one_div,he,Real.sinh_eq]
  have hπ := mul_le_mul (show π/2≤(4 : ℝ)/2 by linarith only [pi_lt_four.le]) hs hs' (by norm_num)
  have H := mul_le_mul_of_nonneg_right hπ hm'.le
  unfold EvaluationPlan.scalarCost
  rw [hmoment]
  calc
    _ ≤ (P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+((P.rates.baseCost : ℝ)+P.rates.ordinary+
        4/2*(x/(1-(P.rates.hStar : ℝ)^2))*P.rates.moment)+(P.rates.rowSquare : ℝ)*x)-c/2 := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left _ P.degree_scale_pos.le
      linarith only [H]
    _ = _ := by
      have hden : 0<1-(P.rates.hStar : ℝ)^2 := by nlinarith only [mul_pos (sub_pos.mpr h1') (by linarith : 0<1+(P.rates.hStar : ℝ))]
      unfold RateData.secondaryLower
      push_cast
      dsimp only [x]
      field_simp [P.degree_scale_pos.ne',P.length_pos.ne',hden.ne']
      <;> ring

theorem secondary_rate {z : ℕ → ℂ} (hne : ∀ i, (π : ℂ)≠z i)
    (hv : ∀ᶠ i in atTop, 0<reducedEvaluation (W.witness i).integral (z i)) {C c : ℝ}
    (hroot : Tendsto (fun i => cappedProximity C (S.X i) π (z i)) atTop (𝓝 c))
    (hc : 0≤c) (hY : c≤(P.rates.Y : ℝ)) :
    UpperRate atTop (S.normRate (fun i => log (reducedEvaluation (W.witness i).integral (z i))))
      ((P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+P.rates.baseCost+P.rates.ordinary)-(P.rates.secondaryLower : ℝ)*c) := by
  rcases hc.eq_or_lt with hzero|hp
  · rw [← hzero,mul_zero,sub_zero]
    exact S.log_unit hv
  let x := c/((P.rates.scale : ℝ)*P.rates.length)
  let r := exp (-x)
  obtain ⟨hr,hr1,he,hcost⟩ := scalar_radius (P := P) hp hY
  have hprice : pricedMinimum (c/2) c 0=c/2 := by
    simp only [pricedMinimum,show 2*(c/2)-c-0=0 by ring,zero_pow (by decide : 2≠0),zero_div,sub_zero]
  have hpen : c/2≤log (1/r)*((P.rates.length : ℝ)*P.rates.scale)/2 := by
    rw [he]
    apply le_of_eq
    field_simp [P.length_pos.ne',P.degree_scale_pos.ne']
    <;> ring
  have H := S.priced_rate hne hv hroot hp le_rfl (half_pos hp) (le_refl (0 : ℝ)) (by linarith : 2*(c/2)≤3*c+0)
    (by simp : (0 : ℝ)≤0*(P.rates.scale : ℝ)) hpen hr hr1.le (W.scalar_minor_rate hr hr1)
  rw [hprice,he] at H
  exact H.mono (Eventually.of_forall (fun _ => le_rfl)) hcost

end PiPolynomialValues.EvaluationScale
