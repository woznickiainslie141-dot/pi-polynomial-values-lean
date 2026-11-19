module

public import OddPiPowers.PolynomialValues.Analysis.ScalarMinor

/-! At any interior scalar radius the entire secondary cost depends on
its hyperbolic sine and on the verified total quantile moment. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Real Polynomial

noncomputable def EvaluationPlan.scalarCost (P : EvaluationPlan) (r : ℝ) :=
  (P.rates.baseCost : ℝ)+P.rates.ordinary+π/2*radiusMoment r*P.rates.moment

theorem EvaluationPlan.totalCutMoment (P : EvaluationPlan) :
    (∑ k : Fin P.cuts.length, 2*(cutMomentQ P.shape (P.cuts.get k) : ℝ))=(P.rates.length : ℝ)*P.rates.moment := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (of_decide_eq_true P.moments).1
  simp only [Rat.cast_sum,cutWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,← sum_div] at h
  exact ((div_eq_iff P.length_pos.ne').mp h).trans (mul_comm _ _)

namespace SelectedSequence

variable {P : EvaluationPlan} (W : SelectedSequence P)

theorem scalar_minor_rate {r : ℝ} (hr : 0<r) (hr1 : r<1) : W.minorRate r (P.scalarCost r) 0 := by
  intro ε hε
  let η := ε/8
  have hη : 0<η := by dsimp [η]; positivity
  let L := (P.rates.length : ℝ)
  let E := Classical.choice P.zeroRate
  let S := ∑ j : Fin P.cuts.length, π/2*(2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))
  have hS : S=π/2*(L*(P.rates.moment : ℝ)) := by rw [← P.totalCutMoment,mul_sum]
  have hlim := (correctionMean_limit hr hr1).mul_const S
  obtain ⟨a,ha⟩ := (hlim.eventually (gt_mem_nhds (show radiusMoment r*S<radiusMoment r*S+η by linarith))).exists
  let t := innerRadius a
  let p (u : Fin P.groups.flatten.length) := scalarPath P r t (scannedNode P.groups u)
  have hp₀ (u : Fin P.groups.flatten.length) := P.paths hr (innerRadius_bounds a).1.le (innerRadius_bounds a).2
    (fun _ => (0 : ℂ[X])) (fun _ => by simp) u
  obtain ⟨K,hK,hv,hp⟩ := P.common_path_bound p (fun u => (hp₀ u).1)
  obtain ⟨k,hb,href⟩ := ((W.block_fit hη).and (W.reference_eventual E hη)).exists
  have hcap := ((W.gapTail_limit (fun _ => π/2)).const_mul (correctionMean r t)).eventually (gt_mem_nhds ha)
  filter_upwards [hb,href,hcap,W.positive_rows,W.mass_atTop.eventually (eventually_ge_atTop 2),
    W.small_overhead K hK P.shape.widths.length P.groups.flatten.length hη] with i hB hR hT hm hN hO
  intro h
  obtain ⟨q,hq⟩ := W.scalar_sample hr hr1 (innerRadius_bounds a).1.le (innerRadius_bounds a).2 i k hm hN E hK
    (fun u c => hv u (W.grid i) (W.frequency i c)) hp h
  refine ⟨q,hq.trans (exp_le_exp.mpr ?_)⟩
  let N := W.mass i
  let n := W.size i
  let b := ∑ u, blockScaleCost N (innerRadius k) ((W.witness i).count u)
  have hsum : b+W.finiteReference E k i+correctionMean r t*W.gapTail i (fun _ => π/2)≤L*P.scalarCost r+3*η := by
    change b≤L*(P.rates.baseCost : ℝ)+η at hB
    change W.finiteReference E k i<L*(P.rates.ordinary : ℝ)+η at hR
    change correctionMean r t*W.gapTail i (fun _ => π/2)<radiusMoment r*S+η at hT
    rw [hS] at hT
    unfold EvaluationPlan.scalarCost
    linarith only [hB,hR.le,hT.le]
  have hslack : N^2*(4*η)≤N^2*ε := mul_le_mul_of_nonneg_left (by dsimp [η]; linarith) (sq_nonneg N)
  simp only [mul_zero,sub_zero]
  linear_combination hO+(N^2)*hsum+hslack

end SelectedSequence
end PiPolynomialValues
