module

public import OddPiPowers.PolynomialValues.Analysis.ConjugateEvaluation
public import OddPiPowers.PolynomialValues.Analysis.RootSelection

/-! Combine the conjugate estimates for one polynomial. When its
degree is smaller than the design degree, positivity of the ordinary
cost gives exactly the required comparison with the design ledger. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod Finset Filter Real Polynomial
open scoped Topology

theorem EvaluationPlan.cost_for_degree (P : EvaluationPlan) {k : ℕ} (hk : k+1≤P.rates.degree) :
    (P.rates.primeCost : ℝ)+P.angularCost+(P.rates.rowSquare : ℝ)*log (1/(P.rates.radius : ℝ))+
      (k : ℝ)*((P.rates.primeCost : ℝ)+P.rates.baseCost+P.rates.ordinary)≤(P.rates.cost : ℝ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hcost,_⟩ := P.tests
  have hp := (Rat.cast_nonneg (K := ℝ)).mpr hcost
  push_cast at hp
  have hk' : (k : ℝ)+1≤(P.rates.degree : ℝ) := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_right (show (k : ℝ)≤(P.rates.degree : ℝ)-1 by linarith) hp
  have hc := P.design.actual_cost P.shape P.cuts P.rates P.arcs P.valid P.checked_arcs P.costs P.base
  unfold EvaluationPlan.angularCost EvaluationPlan.sineCost
  linarith only [hc,hh]

theorem EvaluationScale.resultant_rate_contradiction {P : EvaluationPlan} {W : SelectedSequence P}
    (S : EvaluationScale W) {k : ℕ} (hk : k+1≤P.rates.degree) (z : ℕ → Fin (k+1) → ℂ)
    (b : Fin (k+1) → ℝ) (hn : ∀ i j, (π : ℂ)≠z i j)
    (hb : ∀ j, 0≤b j) (hsec : (∑ j : Fin k, b j.succ)≤k)
    (hmain : (P.rates.target : ℝ)-(∑ j : Fin k, b j.succ)≤b 0) {C : ℝ}
    (H : ∀ j, Tendsto (fun i => cappedProximity C (S.X i) π (z i j)) atTop (𝓝 (b j)))
    (hobs : ∀ᶠ i in atTop, (∀ j, 0<reducedEvaluation (W.witness i).integral (z i j)) ∧
      0≤((W.witness i).integral.natDegree : ℝ)*S.X i+
        ∑ j, log (reducedEvaluation (W.witness i).integral (z i j))) : False := by
  let y := ∑ j : Fin k, b j.succ
  let f (j : Fin (k+1)) (i : ℕ) := log (reducedEvaluation (W.witness i).integral (z i j))
  let A := (P.rates.primeCost : ℝ)+P.rates.baseCost+P.rates.ordinary
  let U := (P.rates.scale : ℝ)*A
  have hy : 0≤y := sum_nonneg (fun j _ => hb j.succ)
  have hY : y≤(P.rates.Y : ℝ) := by
    unfold RateData.Y
    push_cast
    have hk' : (k : ℝ)+1≤(P.rates.degree : ℝ) := by exact_mod_cast hk
    linarith only [hk',hsec]
  have hpos (j : Fin (k+1)) := hobs.mono (fun _ h => h.1 j)
  have HM := S.principal_rate (fun i => hn i 0) (hpos 0) (H 0) hY hmain
  have HS (j : Fin k) : UpperRate atTop (S.normRate (f j.succ)) (U-(P.rates.secondaryLower : ℝ)*b j.succ) :=
    S.secondary_rate (fun i => hn i j.succ) (hpos j.succ) (H j.succ) (hb _) ((single_le_sum
      (s := univ) (f := fun j : Fin k => b j.succ) (fun j _ => hb j.succ) (mem_univ j)).trans hY)
  have HF := UpperRate.sum univ (fun j : Fin k => S.normRate (f j.succ))
    (fun j => U-(P.rates.secondaryLower : ℝ)*b j.succ) (fun j _ => HS j)
  simp only [sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_sum] at HF
  have Hall := (W.degree_rate.add HM).add HF
  have hzero := Hall.nonneg_limit (by
    filter_upwards [hobs,S.positive] with i hi hp
    have hx := div_nonneg hi.2 (mul_nonneg hp.2.2.le hp.1.le)
    rw [Fin.sum_univ_succ,add_div,add_div] at hx
    change 0≤_/(W.size i : ℝ)+S.normRate (f 0) i+∑ j : Fin k, S.normRate (f j.succ) i
    unfold EvaluationScale.normRate
    rw [← sum_div]
    convert hx using 1
    dsimp only [f]
    field_simp [hp.1.ne',hp.2.2.ne']
    <;> ring)
  have hbound := mul_le_mul_of_nonneg_left (P.cost_for_degree hk) P.degree_scale_pos.le
  have hmargin := P.rates.resultant_margin P.margin P.tests hy hY
  have hm : 0<(P.margin : ℝ) := by exact_mod_cast P.margin_pos
  dsimp only [U,A,y] at *
  linarith only [hzero,hbound,hmargin,hm]

end PiPolynomialValues
