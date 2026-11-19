module

public import OddPiPowers.PolynomialValues.Analysis.MinorRates
public import OddPiPowers.PolynomialValues.Analysis.EvaluationScale

/-! Compare the exact finite origin price with its limiting coefficients.
The discrepancy is uniform over all Taylor labels and lower labels. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Real
open scoped Topology

private theorem unit_weight_price {m : ℝ} (hm : 0≤m) (hm1 : m≤1) (a b : ℝ) :
    m*a≤m*b+max 0 (a-b) := by
  have h₁ := mul_le_mul_of_nonneg_left (le_max_right 0 (a-b)) hm
  have h₂ := mul_le_mul_of_nonneg_right hm1 (le_max_left 0 (a-b))
  linarith only [h₁,h₂]

namespace EvaluationScale

variable {P : EvaluationPlan} {W : SelectedSequence P} (S : EvaluationScale W)

noncomputable def originDrift (B δ D fee : ℝ) (i : ℕ) :=
  max 0 (δ-fee*(W.mass i/S.X i))+max 0 (B-D*((W.size i : ℝ)/S.X i)/2)+B/W.size i

theorem originDrift_limit {B δ D fee : ℝ} (hδ : δ≤fee*(P.rates.scale : ℝ))
    (hB : B≤D*((P.rates.length : ℝ)*P.rates.scale)/2) :
    Tendsto (S.originDrift B δ D fee) atTop (𝓝 0) := by
  have h₁ := (tendsto_const_nhds (x := (0 : ℝ))).max ((S.ratio.const_mul fee).const_sub δ)
  have h₂ := (tendsto_const_nhds (x := (0 : ℝ))).max (((S.columns_ratio.const_mul D).div_const 2).const_sub B)
  have h₃ := (tendsto_inv_atTop_zero.comp W.size_atTop).const_mul B
  rw [max_eq_left (sub_nonpos.mpr hδ)] at h₁
  rw [max_eq_left (sub_nonpos.mpr hB)] at h₂
  have H := (h₁.add h₂).add h₃
  simp only [mul_zero,add_zero] at H
  apply H.congr
  intro i
  change _=max 0 (δ-fee*(W.mass i/S.X i))+max 0 (B-D*((W.size i : ℝ)/S.X i)/2)+B/W.size i
  simp only [Function.comp_apply,div_eq_mul_inv]

theorem finite_origin_credit (i : ℕ) (hx : 0<S.X i) (hn : 0<(W.size i : ℝ))
    (h : LabelChoice (W.layer i)) (q : LabelChoice (fun c => (h c).val)) {B c δ : ℝ}
    (hB : 0<B) (hc : 0≤c) (hδ : 0≤δ) (hhi : 2*B≤3*c+δ) (D fee : ℝ) {η : ℝ} (hη : 0≤η) :
    (W.size i : ℝ)*S.X i*(pricedMinimum B c δ-(P.shape.widths.length : ℝ)*η-S.originDrift B δ D fee i)≤
      W.totalLabel i h*((c-η)*S.X i)+W.mass i*W.markCount i h*fee+
      (labelPairs (fun j => (q j).val) : ℝ)*D := by
  let n := (W.size i : ℝ)
  let X := S.X i
  let M := W.markCount i h
  let H := W.totalLabel i h
  let Q := (labelPairs (fun j => (q j).val) : ℝ)
  let V := 2*Q/n^2
  let J := (P.shape.widths.length : ℝ)
  have hm := W.markCount_bounds i h
  have hq := SelectedSequence.small_label_pairs (W.layer i) (fun u => ((W.witness i).colIndex u).1.isLt.le) h q
  have hH := W.totalLabel_bounds i h
  have H₁ := unit_weight_price (div_nonneg hm.1 hn.le) ((div_le_one hn).mpr hm.2) δ (fee*(W.mass i/X))
  have H₂ := unit_weight_price (m := V) (div_nonneg (mul_nonneg (by norm_num) hq.1) (sq_nonneg _))
    ((div_le_one (sq_pos_of_pos hn)).mpr hq.2) B (D*(n/X)/2)
  have H₃ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hn).mpr (hH.2.trans_eq (mul_comm _ _))) hη
  have hprice := chosen_origin_price (Nat.cast_pos.mp hn) (W.layer i)
    (fun u => ((W.witness i).colIndex u).1.isLt.le) h q hB hc hδ hhi
  change pricedMinimum B c δ≤(H*c+M*δ)/n+B*(2*Q+n)/n^2 at hprice
  have hsplit : (H*c+M*δ)/n+B*(2*Q+n)/n^2=H/n*c+M/n*δ+V*B+B/n := by
    dsimp only [V]; field_simp [hn.ne']; ring
  rw [hsplit] at hprice
  change M/n*δ≤M/n*(fee*(W.mass i/X))+_ at H₁
  change H/n*η≤J*η at H₃
  change V*B≤V*(D*(n/X)/2)+_ at H₂
  have he : pricedMinimum B c δ-J*η-S.originDrift B δ D fee i≤
      H/n*(c-η)+M/n*(fee*(W.mass i/X))+V*(D*(n/X)/2) := by
    unfold originDrift
    change pricedMinimum B c δ-J*η-(max 0 (δ-fee*(W.mass i/X))+max 0 (B-D*(n/X)/2)+B/n)≤_
    linarith only [hprice,H₁,H₂,H₃]
  apply (mul_le_mul_of_nonneg_left he (mul_nonneg hn.le hx.le)).trans_eq
  change n*X*(H/n*(c-η)+M/n*(fee*(W.mass i/X))+V*(D*(n/X)/2))=H*((c-η)*X)+W.mass i*M*fee+Q*D
  dsimp only [V]
  field_simp [show n≠0 from hn.ne',show X≠0 from hx.ne']
  <;> ring

end EvaluationScale
end PiPolynomialValues
