module

public import OddPiPowers.PolynomialValues.Analysis.OriginPriceLimit
public import OddPiPowers.PolynomialValues.ConjugateTaylorDecay

/-! The same selected Gaussian polynomial is evaluated at a conjugate
with positive proximity. The estimate sums every Taylor label before
passing to the normalized logarithm. -/

@[expose] public section

namespace PiPolynomialValues.EvaluationScale

open FourPeriod Finset Filter Real
open scoped Topology

variable {P : EvaluationPlan} {W : SelectedSequence P} (S : EvaluationScale W)

private theorem choice_exponential {n J : ℕ} (j : Fin n → ℕ) (hj : ∀ u, j u≤J) :
    (Fintype.card (LabelChoice j) : ℝ)≤exp ((n : ℝ)*log ((J : ℝ)+1)) := by
  rw [exp_nat_mul,exp_log (by positivity : 0<(J : ℝ)+1)]
  exact_mod_cast labelChoice_count j hj

theorem finite_priced_log (i : ℕ) (z : ℂ) (hz : 1≤‖z‖) (hv : 0<reducedEvaluation (W.witness i).integral z)
    (hx : 0<S.X i) (hn : 0<(W.size i : ℝ)) {B c δ r E fee η : ℝ}
    (hB : 0<B) (hc : 0≤c) (hδ : 0≤δ) (hhi : 2*B≤3*c+δ) (hη : 0≤η)
    (hpert : ‖Complex.I*(z-(π : ℂ))/2‖≤exp (-((c-η)*S.X i)))
    (hm : ∀ h : LabelChoice (W.layer i), ∃ q : LabelChoice (fun u => (h u).val),
      ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤exp
        ((W.mass i)^2*((P.rates.length : ℝ)*E+η)-W.mass i*W.markCount i h*fee+
          ((W.order i : ℝ)-labelPairs (fun u => (q u).val))*log (1/r))) :
    log (reducedEvaluation (W.witness i).integral z)≤
      log ((W.witness i).denominator : ℝ)+(W.size i : ℝ)*
        (log ((P.shape.widths.length : ℝ)+1)+(P.shape.widths.length : ℝ)*log 2)+
      (W.mass i)^2*((P.rates.length : ℝ)*E+η)+(W.order i : ℝ)*log (1/r)+
      (W.size i : ℝ)*S.X i*(-pricedMinimum B c δ+(P.shape.widths.length : ℝ)*η+S.originDrift B δ (log (1/r)) fee i) := by
  classical
  let n := W.size i
  let J := P.shape.widths.length
  let D := log (1/r)
  let X := S.X i
  let p := Complex.I*(z-(π : ℂ))/2
  let M (h : LabelChoice (W.layer i)) := W.minor i h (fun u => phasePoint (scannedNode P.groups u))
  let T := (n : ℝ)*J*log 2+(W.mass i)^2*((P.rates.length : ℝ)*E+η)+(W.order i : ℝ)*D+
    (n : ℝ)*X*(-pricedMinimum B c δ+(J : ℝ)*η+S.originDrift B δ D fee i)
  have hj (u : Fin n) : W.layer i u≤J := ((W.witness i).colIndex u).1.isLt.le
  have hterm (h : LabelChoice (W.layer i)) : ‖labelCoefficient (W.layer i) h p‖*‖M h‖≤exp T := by
    obtain ⟨q,hq⟩ := hm h
    have H := mul_le_mul (perturbation_coefficient _ h hj hpert) hq (norm_nonneg _) (exp_pos _).le
    have hprice := S.finite_origin_credit i hx hn h q hB hc hδ hhi D fee hη
    apply H.trans
    rw [← exp_add,exp_le_exp]
    change _-W.totalLabel i h*((c-η)*X)+(_-W.mass i*W.markCount i h*fee+
      ((W.order i : ℝ)-(labelPairs (fun j => (q j).val) : ℝ))*D)≤T
    dsimp only [T]
    linear_combination hprice
  have hsum := sum_le_sum (s := univ) (fun h _ => hterm h)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_right (choice_exponential (W.layer i) hj) (exp_pos T).le)
  rw [← exp_add] at hbound
  let w := W.witness i
  have he := w.eval_le_centered_labels (P.nested _) (centeredGridValue P.shape P.anchor (W.grid i)) z hz
  change ‖w.integral.eval₂ GaussianInt.toComplex z‖≤(w.denominator : ℝ)*
    ∑ h, ‖labelCoefficient (W.layer i) h p‖*‖M h‖ at he
  have hd : 0<(w.denominator : ℝ) := by exact_mod_cast w.denominator_pos
  have hr : reducedEvaluation w.integral z≤‖w.integral.eval₂ GaussianInt.toComplex z‖ :=
    div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_rootScale z))
  have hl := log_le_log hv ((hr.trans he).trans (mul_le_mul_of_nonneg_left hbound hd.le))
  rw [log_mul hd.ne' (exp_pos _).ne',log_exp] at hl
  exact hl.trans_eq (by dsimp only [T,n,J,X,D,w]; ring)

theorem order_scaled : UpperRate atTop (S.normRate (fun i => (W.order i : ℝ)))
    ((P.rates.scale : ℝ)*P.rates.rowSquare) := by
  have H := W.order_upper.mul_scale S.mass_factor (S.positive.mono (fun i hi =>
    div_nonneg (sq_nonneg _) (mul_nonneg hi.2.2.le hi.1.le))) (div_nonneg P.degree_scale_pos.le P.length_pos.le)
  apply H.mono
  · filter_upwards [S.positive] with i hi
    apply le_of_eq
    unfold normRate
    field_simp [hi.1.ne',hi.2.1.ne',hi.2.2.ne']
  · apply le_of_eq
    field_simp [P.length_pos.ne']

theorem priced_rate {z : ℕ → ℂ} (hne : ∀ i, (π : ℂ)≠z i)
    (hv : ∀ᶠ i in atTop, 0<reducedEvaluation (W.witness i).integral (z i))
    {C b B c δ r E fee : ℝ} (hroot : Tendsto (fun i => cappedProximity C (S.X i) π (z i)) atTop (𝓝 b))
    (hc : 0<c) (hb : c≤b) (hB : 0<B) (hδ : 0≤δ) (hhi : 2*B≤3*c+δ)
    (hfee : δ≤fee*(P.rates.scale : ℝ)) (hpen : B≤log (1/r)*((P.rates.length : ℝ)*P.rates.scale)/2)
    (hr : 0<r) (hr1 : r≤1) (hm : W.minorRate r E fee) :
    UpperRate atTop (S.normRate (fun i => log (reducedEvaluation (W.witness i).integral (z i))))
      ((P.rates.scale : ℝ)*((P.rates.primeCost : ℝ)+E+(P.rates.rowSquare : ℝ)*log (1/r))-pricedMinimum B c δ) := by
  let L := (P.rates.length : ℝ)
  let J := (P.shape.widths.length : ℝ)
  let D := log (1/r)
  let A := log (J+1)+J*log 2
  have hD : 0≤D := log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hr1))
  apply UpperRate.of_relaxed (K := (P.rates.scale : ℝ)/L+J)
  intro η hη
  have h₀ := (tendsto_inv_atTop_zero.comp S.grow).const_mul A
  simp only [mul_zero] at h₀
  have horder := S.order_scaled.mul_scale (tendsto_const_nhds (x := D)) (Eventually.of_forall (fun _ => hD)) hD
  have hconstant := tendsto_const_nhds (f := atTop (α := ℕ)) (x := -pricedMinimum B c δ+J*η)
  have H₁ := S.scaled_prime.add (UpperRate.of_tendsto h₀)
  have H₂ := H₁.add (UpperRate.of_tendsto (S.mass_factor.mul_const (L*E+η)))
  have H := (H₂.add horder).add (UpperRate.of_tendsto (hconstant.add (S.originDrift_limit hfee hpen)))
  apply H.mono
  · filter_upwards [S.positive,hv,conjugate_taylor_decay S.grow hne hroot hc hb hη,hm η hη] with i hi hv' hp' hm'
    have hf := S.finite_priced_log i (z i) hp'.1 hv' hi.1 hi.2.2 hB hc.le hδ hhi hη.le hp'.2 hm'
    apply (div_le_div_of_nonneg_right hf (mul_nonneg hi.2.2.le hi.1.le)).trans_eq
    dsimp only [normRate,Function.comp_def,A,J,L,D]
    field_simp [hi.1.ne',hi.2.2.ne']
    <;> ring
  · apply le_of_eq
    dsimp only [L,D]
    field_simp [P.length_pos.ne']
    <;> ring

end PiPolynomialValues.EvaluationScale
