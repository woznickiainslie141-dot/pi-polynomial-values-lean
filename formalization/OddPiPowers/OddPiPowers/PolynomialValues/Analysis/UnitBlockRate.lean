module

public import OddPiPowers.PolynomialValues.Analysis.AllocatedBlockRate
public import OddPiPowers.PolynomialValues.Analysis.SelectedEvaluation

/-! On the unit circle the original reduced polynomial has phase factors
of modulus one. The same zero-direction spatial reference bounds the
allocated energy for every point of that circle. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real

theorem unit_column_bound {m n j J : ℕ} (hm : m≤n) (hj : j≤J) (z : ℂ) {K : ℝ} (hK : 1≤K) (hz : ‖z‖≤K) :
    (2 : ℝ)^j*(‖z‖+blockGrowth m)^j≤exp (columnOverhead K n J) := by
  have h := center_column_bound (h := 0) hm hj (Nat.zero_le j) 0 0 0 z hK (by simpa using (zero_le_one.trans hK)) hz
  simpa only [centerAmplitude,Int.cast_zero,sub_self,pow_zero,mul_one,zero_mul,Complex.exp_zero,
    norm_pow,Complex.norm_ofNat,Nat.sub_zero,zero_add] using h

theorem unit_allocated_rate {n V J : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (hV : 0<V) (hm : ∀ u, 0<m u ∧ m u≤n) (x : Fin n → ℤ) (j : Fin n → ℕ) (hj : ∀ c, j c≤J)
    (z A : Fin V → Fin n → ℂ) (hA : ∀ u c, ‖A u c‖=(2 : ℝ)^j c) {K : ℝ} (hK : 1≤K)
    (hp : ∀ u c, ‖z u c‖≤K) {N r : ℝ} (hN : 2≤N) (hr : 0<r) (hr1 : r<1)
    (y : Fin n → FrequencyInterval) (hx : ∀ i, (x i : ℝ)=N*(y i : ℝ)) :
    ∃ θ : Equiv.Perm (Fin n), ‖(pathMatrix e x j z A).det‖≤
      exp ((n : ℝ)*(log V+columnOverhead K n J)+N^2*∑ u, (blockScaleCost N r (m u)+
        radialInteraction unitFrequency r (allocationCharge m (allocationEquiv e θ) y N u)
          (allocationCharge m (allocationEquiv e θ) y N u)/2)) := by
  obtain ⟨θ,hθ⟩ := pathMatrix_bound e x j z A
  let c := allocatedColumn e θ
  let H := columnOverhead K n J
  let P := allocationCharge m (allocationEquiv e θ) y N
  let F (u : Fin V) := blockScaleCost N r (m u)+radialInteraction unitFrequency r (P u) (P u)/2
  let B (u : Fin V) := factorialWeight (m u)*(∏ i, ‖A u (c u i)‖)*
    (pairEnvelope (x ∘ c u)*∏ i, (‖z u (c u i)‖+blockGrowth (m u))^j (c u i))
  have h₀ (u : Fin V) : 0≤B u := mul_nonneg (mul_nonneg (factorialWeight_pos _).le (prod_nonneg fun _ _ => norm_nonneg _))
    (mul_nonneg (pairEnvelope_nonneg _) (prod_nonneg fun _ _ => by positivity))
  have hb (u : Fin V) : B u≤exp (N^2*F u+(m u : ℝ)*H) := by
    have h := separated_block_bound (hm u).1 (x ∘ c u) (y ∘ c u) hN hr hr1 (fun i => hx (c u i))
      (fun i => ‖A u (c u i)‖) (fun i => (‖z u (c u i)‖+blockGrowth (m u))^j (c u i))
      (fun _ => H) (fun _ => norm_nonneg _) (fun _ => by positivity) (fun i => by
        rw [hA]; exact unit_column_bound (hm u).2 (hj _) _ hK (hp _ _))
    simpa only [B,F,P,c,allocationCharge,allocationEquiv,allocatedColumn,Equiv.trans_apply,
      Function.comp_def,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have hcard : (∑ u, m u)=n := by simpa [RowCandidates,Fintype.card_sigma] using (Fintype.card_congr e).symm
  refine ⟨θ,hθ.trans ((mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun u _ => h₀ u) (fun u _ => hb u)) (by positivity)).trans_eq ?_)⟩
  rw [← Real.exp_sum,← Real.exp_log (show 0<(V : ℝ)^n by positivity),← exp_add,log_pow,
    sum_add_distrib,← mul_sum,← sum_mul,← Nat.cast_sum,hcard]
  congr 1
  change (n : ℝ)*log V+(N^2*(∑ u, F u)+(n : ℝ)*H)=_
  dsimp only [F,H,P]
  ring

end PiPolynomialValues.FourPeriod
