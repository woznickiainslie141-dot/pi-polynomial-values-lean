module

public import OddPiPowers.PolynomialValues.Analysis.MinorPoissonMean

/-! The priced angular estimate at the principal radius, for all Taylor
labels and each selected polynomial after a single scale threshold. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Filter Real MeasureTheory Polynomial
open scoped Topology

variable {P : EvaluationPlan} (W : SelectedSequence P)

theorem scaled_markCount (i : ℕ) (h : LabelChoice (W.layer i)) (hm : 0<W.mass i) :
    (W.mass i)^2*markedMass (fun j => (h j).val) (W.mass i)=W.mass i*W.markCount i h := by
  unfold markedMass markCount
  rw [← mul_assoc,show (W.mass i)^2*(W.mass i)⁻¹=W.mass i by field_simp]

theorem small_overhead (K : ℝ) (hK : 1≤K) (J V : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ i in atTop, (W.size i : ℝ)*(log V+columnOverhead K (W.size i) J)+1≤(W.mass i)^2*η := by
  have hi := (tendsto_inv_atTop_zero.comp W.mass_atTop).pow 2
  have H := (W.overhead_limit K hK J V).add hi
  simp only [zero_pow (by decide : 2≠0),add_zero] at H
  filter_upwards [H.eventually (gt_mem_nhds hη),W.mass_atTop.eventually (eventually_gt_atTop 0)] with i h hp
  have h' : ((W.size i : ℝ)*(log V+columnOverhead K (W.size i) J)+1)/(W.mass i)^2≤η := by
    rw [add_div,one_div,← inv_pow]
    exact h.le
  exact (div_le_iff₀ (sq_pos_of_pos hp)).mp h' |>.trans_eq (mul_comm _ _)

theorem primary_minor_rate : W.minorRate P.rates.radius P.angularCost P.rates.labelPrice := by
  intro ε hε
  let η := ε/8
  have hη : 0<η := by dsimp [η]; positivity
  let r := (P.rates.radius : ℝ)
  let L := (P.rates.length : ℝ)
  let F (j : Fin P.cuts.length) := P.design.directionForm j.val
  have hr := P.radius_bounds
  obtain ⟨g,t,ht,ht1,hg,hcost⟩ := P.correction_choice hη
  let p (u : Fin P.groups.flatten.length) := incrementFamily r t g (scannedNode P.groups u)
  obtain ⟨K,hK,hv,hp⟩ := P.common_path_bound p (fun u => (P.paths hr.1 ht.le ht1 g (fun j => (hg j).1) u).1)
  obtain ⟨k,hb,href⟩ := ((W.block_fit hη).and (W.references_fit hη)).exists
  let err := ∫ z, slopeError g F z ∂poissonLaw r
  let A := correctionMean r t
  let a (j : Fin P.cuts.length) := pathGap r (g j)
  let S := ∑ j, a j*(2*(cutMomentQ P.shape (P.cuts.get j) : ℝ))
  have hC : err*L+A*S<L*P.sineCost+2*η := by
    change L*err+A*S≤L*P.sineCost+η at hcost
    rw [mul_comm err]
    linarith only [hcost,hη]
  have ha := ((W.length_limit.const_mul err).add ((W.gapTail_limit a).const_mul A)).eventually (gt_mem_nhds hC)
  have hfee := (P.design.actual_direction_price P.shape P.cuts P.rates P.arcs P.valid P.checked_arcs P.costs).2
  filter_upwards [hb,href,ha,W.positive_rows,W.mass_atTop.eventually (eventually_ge_atTop 2),
    W.small_overhead K hK P.shape.widths.length P.groups.flatten.length hη] with i hB hfit hA hrows hN hO
  intro h
  obtain ⟨q,hq⟩ := W.angular_sample i k hrows hN hfit ht.le ht1 g hg hK
    (fun u c => hv u (W.grid i) (W.frequency i c)) hp h
  refine ⟨q,hq.trans (exp_le_exp.mpr ?_)⟩
  let N := W.mass i
  let n := W.size i
  let M := markedMass (fun j => (h j).val) N
  let E := P.design.energyForm.actual P.rates.radius false
  let cost := ∑ u, blockScaleCost N (innerRadius k) ((W.witness i).count u)
  have hM : N^2*M=N*W.markCount i h := W.scaled_markCount i h (by linarith)
  have hprice := mul_le_mul_of_nonneg_left hfee (mul_nonneg (show 0≤N by dsimp [N]; linarith) (W.markCount_bounds i h).1)
  have hsum : cost+L*E+η+err*W.lengthRatio i+A*W.gapTail i a≤L*P.angularCost+4*η := by
    change cost≤L*(P.rates.baseCost : ℝ)+η at hB
    change err*W.lengthRatio i+A*W.gapTail i a<L*P.sineCost+2*η at hA
    unfold EvaluationPlan.angularCost
    dsimp only [E,L] at *
    linarith only [hB,hA.le]
  have hscale := mul_le_mul_of_nonneg_left hsum (sq_nonneg N)
  have hslack : N^2*(5*η)≤N^2*ε := mul_le_mul_of_nonneg_left (by dsimp [η]; linarith) (sq_nonneg N)
  change _+((n : ℝ)*_+N^2*(cost+L*E+η-M*P.design.priceForm.actual P.rates.radius false+
    err*W.lengthRatio i+A*W.gapTail i a))+1≤N^2*(L*P.angularCost+ε)-N*W.markCount i h*(P.rates.labelPrice : ℝ)+_
  linear_combination hO+hscale+hprice+hslack-(P.design.priceForm.actual P.rates.radius false)*hM

end PiPolynomialValues.SelectedSequence
