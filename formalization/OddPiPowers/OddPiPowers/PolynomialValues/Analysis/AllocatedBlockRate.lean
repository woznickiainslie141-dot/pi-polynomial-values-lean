module

public import OddPiPowers.PolynomialValues.Analysis.BlockAmplitude
public import OddPiPowers.PolynomialValues.Analysis.AllocationEnergy

/-! The maximizing allocation has a uniform bound in the regularized
energy. A common reflection of every frequency is allowed on one semicircle. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real

def faceFrequency (reflect : Bool) (x : ℤ) := if reflect then -x else x
noncomputable def faceSlope (reflect : Bool) (p : ℂ) := if reflect then -p.re else p.re

noncomputable def linearFrequency (a : ℝ) : C(FrequencyInterval,ℝ) :=
  ⟨fun x => a*(x : ℝ),continuous_const.mul continuous_subtype_val⟩

theorem pairEnvelope_face {m : ℕ} (reflect : Bool) (x : Fin m → ℤ) :
    pairEnvelope (faceFrequency reflect ∘ x)=pairEnvelope x := by
  cases reflect
  · rfl
  · unfold pairEnvelope
    apply prod_congr rfl
    intro e _
    simp only [Function.comp_apply,faceFrequency,if_true,neg_sub_neg,Int.cast_sub]
    rw [norm_sub_rev]

theorem allocated_linear_scale {m : ℕ} (x : Fin m → ℤ) (y : Fin m → FrequencyInterval)
    (reflect : Bool) (p : ℂ) {N : ℝ} (hN : 0 < N) (hx : ∀ i, (faceFrequency reflect (x i) : ℝ)=N*(y i : ℝ))
    (H : ℝ) :
    (∑ i, ((x i : ℝ)*p.re+H))=
      N^2*(atomicCharge y (fun _ => N⁻¹) (linearFrequency (faceSlope reflect p)))+(m : ℝ)*H := by
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,atomicCharge_apply,mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  change (x i : ℝ)*p.re=N^2*(N⁻¹*(faceSlope reflect p*(y i : ℝ)))
  have h := hx i
  have hcancel : N^2*N⁻¹=N := by field_simp
  rw [← mul_assoc,hcancel]
  cases reflect <;> simp [faceFrequency,faceSlope] at h ⊢
  · linear_combination p.re*h
  · linear_combination (-p.re)*h

theorem centeredBlock_nonneg {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m) (θ : Equiv.Perm (Fin n))
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ) (u : Fin V) : 0≤centeredBlockEnvelope e θ v x j a h p u := by
  unfold centeredBlockEnvelope
  exact mul_nonneg (mul_nonneg (factorialWeight_pos _).le (prod_nonneg (fun _ _ => norm_nonneg _)))
    (mul_nonneg (pairEnvelope_nonneg _) (prod_nonneg (fun _ _ => by positivity)))

theorem determinant_allocated_rate {n V J : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (hV : 0 < V) (hm : ∀ u, 0 < m u ∧ m u≤n) (v : Fin V → ℤ) (x : Fin n → ℤ)
    (j : Fin n → ℕ) (hj : ∀ c, j c≤J) (a : ℤ → ℤ) (h : LabelChoice j) (p : Fin V → ℂ)
    {K : ℝ} (hK : 1≤K) (hv : ∀ u c, ‖(v u : ℂ)-(a (x c) : ℂ)‖≤K) (hp : ∀ u, ‖p u‖≤K)
    {N r : ℝ} (hN : 2≤N) (hr : 0 < r) (hr1 : r < 1) (reflect : Bool) (y : Fin n → FrequencyInterval)
    (hx : ∀ i, (faceFrequency reflect (x i) : ℝ)=N*(y i : ℝ)) (hn : (centeredLabelMatrix e v x j a h p).det≠0) :
    ∃ θ : Equiv.Perm (Fin n),
      (∀ u i, (h (allocatedColumn e θ u i)).val≠0 → v u≠a (x (allocatedColumn e θ u i))) ∧
      ‖(centeredLabelMatrix e v x j a h p).det‖≤exp ((n : ℝ)*(log V+columnOverhead K n J)+N^2*
        ∑ u, (blockScaleCost N r (m u)+
          (allocationCharge m (allocationEquiv e θ) y N u) (linearFrequency (faceSlope reflect (p u)))+
          radialInteraction unitFrequency r (allocationCharge m (allocationEquiv e θ) y N u)
            (allocationCharge m (allocationEquiv e θ) y N u)/2)) := by
  obtain ⟨θ,hθ,ho⟩ := centered_positive_allocation e v x j a h p hn
  let P := allocationCharge m (allocationEquiv e θ) y N
  let F (u : Fin V) := blockScaleCost N r (m u)+(P u) (linearFrequency (faceSlope reflect (p u)))+
    radialInteraction unitFrequency r (P u) (P u)/2
  let H := columnOverhead K n J
  have hb (u : Fin V) : centeredBlockEnvelope e θ v x j a h p u≤exp (N^2*F u+(m u : ℝ)*H) := by
    let c := allocatedColumn e θ u
    have hc := separated_block_bound (hm u).1 (faceFrequency reflect ∘ (x ∘ c)) (y ∘ c) hN hr hr1 (fun i => hx (c i))
      (fun i => ‖centerAmplitude (v u) (x (c i)) (a (x (c i))) (j (c i)) (h (c i)).val (p u)‖)
      (fun i => (‖p u‖+blockGrowth (m u))^(j (c i)-(h (c i)).val))
      (fun i => (x (c i) : ℝ)*(p u).re+H) (fun i => norm_nonneg _) (fun i => by positivity)
      (fun i => center_column_bound (hm u).2 (hj (c i)) (Nat.lt_succ_iff.mp (h (c i)).isLt)
        _ _ _ _ hK (hv u (c i)) (hp u))
    have hlin := allocated_linear_scale (x ∘ c) (y ∘ c) reflect (p u) (by linarith) (fun i => hx (c i)) H
    simp only [Function.comp_apply] at hlin
    rw [pairEnvelope_face,hlin] at hc
    apply hc.trans_eq
    congr 1
    change N^2*(_+radialInteraction unitFrequency r (P u) (P u)/2)+
      (N^2*(P u) (linearFrequency (faceSlope reflect (p u)))+(m u : ℝ)*H)=_
    dsimp only [F]
    ring
  have hcard : (∑ u, m u)=n := by simpa [RowCandidates,Fintype.card_sigma] using (Fintype.card_congr e).symm
  refine ⟨θ,ho,hθ.trans ((mul_le_mul_of_nonneg_left (prod_le_prod₀
    (fun u _ => centeredBlock_nonneg e θ v x j a h p u) (fun u _ => hb u)) (by positivity)).trans_eq ?_)⟩
  rw [← Real.exp_sum,← Real.exp_log (show 0 < (V : ℝ)^n by positivity),← exp_add,log_pow,
    sum_add_distrib,← mul_sum,← sum_mul,← Nat.cast_sum,hcard]
  congr 1
  change (n : ℝ)*log V+(N^2*(∑ u, F u)+(n : ℝ)*H)=_
  dsimp only [F,H,P]
  ring

end PiPolynomialValues.FourPeriod
