module

public import OddPiPowers.PolynomialValues.Analysis.CenteredExpansion

/-! The maximizing block allocation for a nonzero centered determinant
assigns every positively labelled column away from its center. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Complex

variable {n V : ℕ} {m : Fin V → ℕ}

noncomputable def centerAmplitude (v t a : ℤ) (j h : ℕ) (p : ℂ) :=
  (2 : ℂ)^j*((v : ℂ)-(a : ℂ))^h*Complex.exp ((t : ℂ)*p)

noncomputable def centeredBlockEnvelope (e : Fin n ≃ RowCandidates m) (θ : Equiv.Perm (Fin n))
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (p : Fin V → ℂ) (u : Fin V) : ℝ :=
  let c := allocatedColumn e θ u
  factorialWeight (m u)*(∏ i, ‖centerAmplitude (v u) (x (c i)) (a (x (c i))) (j (c i)) (h (c i)).val (p u)‖)*
    (pairEnvelope (x ∘ c)*∏ i, (‖p u‖+blockGrowth (m u))^(j (c i)-(h (c i)).val))

theorem centered_positive_allocation (e : Fin n ≃ RowCandidates m) (v : Fin V → ℤ) (x : Fin n → ℤ)
    (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j) (p : Fin V → ℂ)
    (hn : (centeredLabelMatrix e v x j a h p).det ≠ 0) :
    ∃ θ : Equiv.Perm (Fin n),
      ‖(centeredLabelMatrix e v x j a h p).det‖ ≤ (V : ℝ)^n*∏ u, centeredBlockEnvelope e θ v x j a h p u ∧
      ∀ u i, (h (allocatedColumn e θ u i)).val ≠ 0 → v u ≠ a (x (allocatedColumn e θ u i)) := by
  obtain ⟨θ,hθ⟩ := pathMatrix_bound e x (fun c => j c-(h c).val) (fun u _ => p u)
    (fun u c => centerAmplitude (v u) (x c) (a (x c)) (j c) (h c).val (p u))
  change ‖(centeredLabelMatrix e v x j a h p).det‖ ≤ (V : ℝ)^n*∏ u, centeredBlockEnvelope e θ v x j a h p u at hθ
  refine ⟨θ,hθ,?_⟩
  intro u i hh he
  let c := allocatedColumn e θ u
  have ha : centerAmplitude (v u) (x (c i)) (a (x (c i))) (j (c i)) (h (c i)).val (p u)=0 := by
    simp [centerAmplitude,he,c,hh]
  have hp : (∏ i, ‖centerAmplitude (v u) (x (c i)) (a (x (c i))) (j (c i)) (h (c i)).val (p u)‖)=0 :=
    prod_eq_zero (mem_univ i) (by rw [ha,norm_zero])
  have he0 : centeredBlockEnvelope e θ v x j a h p u=0 := by
    unfold centeredBlockEnvelope
    change factorialWeight (m u)*(∏ i, ‖centerAmplitude (v u) (x (c i)) (a (x (c i))) (j (c i)) (h (c i)).val (p u)‖)*_=0
    rw [hp,mul_zero,zero_mul]
  rw [prod_eq_zero (mem_univ u) he0,mul_zero] at hθ
  exact ((norm_pos_iff.mpr hn).not_ge hθ)

noncomputable def allocationEquiv (e : Fin n ≃ RowCandidates m) (θ : Equiv.Perm (Fin n)) :
    RowCandidates m ≃ Fin n := e.symm.trans θ.symm

theorem allocated_sum {A : Type*} [AddCommMonoid A] (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (f : Fin n → A) :
    (∑ u, ∑ i : Fin (m u), f (allocatedColumn e θ u i)) = ∑ c, f c := by
  have he := (allocationEquiv e θ).sum_comp f
  rw [Fintype.sum_sigma] at he
  exact he

theorem allocated_price (e : Fin n ≃ RowCandidates m) (θ : Equiv.Perm (Fin n))
    (v : Fin V → ℤ) (x : Fin n → ℤ) (j : Fin n → ℕ) (a : ℤ → ℤ) (h : LabelChoice j)
    (hθ : ∀ u i, (h (allocatedColumn e θ u i)).val ≠ 0 → v u ≠ a (x (allocatedColumn e θ u i)))
    {fee : ℝ} (hfee : 0 ≤ fee) :
    (∑ c, if (h c).val=0 then 0 else fee) ≤ ∑ u, ∑ i : Fin (m u),
      if j (allocatedColumn e θ u i) ≠ 0 ∧ v u ≠ a (x (allocatedColumn e θ u i)) then fee else 0 := by
  rw [← allocated_sum e θ (fun c => if (h c).val=0 then 0 else fee)]
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro i _
  let c := allocatedColumn e θ u i
  by_cases hh : (h c).val=0
  · change (if (h c).val=0 then 0 else fee) ≤ (if j c≠0 ∧ v u≠a (x c) then fee else 0)
    simp only [hh,if_true]
    split <;> simp [hfee]
  · have hle := (h c).isLt
    have hj : j c ≠ 0 := by omega
    change (if (h c).val=0 then 0 else fee) ≤ (if j c≠0 ∧ v u≠a (x c) then fee else 0)
    have hc : v u ≠ a (x c) := hθ u i hh
    simp [hh,hj,hc]

end PiPolynomialValues.FourPeriod
