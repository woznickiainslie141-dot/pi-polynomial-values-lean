module

public import OddPiPowers.PolynomialValues.FourPeriod.NodeBlockExpansion
import all OddPiPowers.PolynomialValues.FourPeriod.NodeBlockExpansion
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max

/-! The permutation in the node expansion contributes a complex factor
of norm one. One allocation suffices to bound the whole determinant. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

theorem allocation_norm_eq {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → Fin V) (θ : Equiv.Perm (Fin n))
    (hb : ∀ j, (e (θ j)).1 = b j) :
    ‖(nodeMask e A b).det‖ = ∏ v, ‖(allocationBlock e A θ v).det‖ := by
  classical
  let M := nodeMask e A b
  let N := M.submatrix id θ.symm
  have htag (j) : b (θ.symm j) = (e j).1 := by
    simpa only [θ.apply_symm_apply] using (hb (θ.symm j)).symm
  have ht : N.BlockTriangular (fun i => (e i).1) := by
    intro i j h
    change (if (e i).1 = b (θ.symm j) then A i (θ.symm j) else 0) = 0
    rw [htag,if_neg h.ne']
  have he : N.det = ∏ v, (allocationBlock e A θ v).det := by
    rw [ht.det_fintype]
    apply prod_congr rfl
    intro v _
    rw [← Matrix.det_submatrix_equiv_self (prefixFiber e v) _]
    apply congrArg Matrix.det
    ext i j
    change (if (e (e.symm ⟨v,i⟩)).1 = b (θ.symm (e.symm ⟨v,j⟩)) then _ else 0) = _
    rw [htag,e.apply_symm_apply,e.apply_symm_apply,if_pos rfl]
    rfl
  change ‖M.det‖ = _
  rw [← norm_prod,← he]
  change ‖M.det‖ = ‖(M.submatrix id θ.symm).det‖
  rw [Matrix.det_permute',norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign θ.symm) with h | h <;> simp [h]

theorem exists_node_norm_bound {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ θ : Equiv.Perm (Fin n), ‖A.det‖ ≤ (V : ℝ)^n * ∏ v, ‖(allocationBlock e A θ v).det‖ := by
  classical
  let f (θ : Equiv.Perm (Fin n)) := ∏ v, ‖(allocationBlock e A θ v).det‖
  obtain ⟨θ,_,hθ⟩ := univ.exists_max_image f univ_nonempty
  refine ⟨θ,?_⟩
  calc
    ‖A.det‖ = ‖∑ b : Fin n → Fin V, (nodeMask e A b).det‖ := congrArg _ (det_by_node_allocations e A)
    _ ≤ ∑ b : Fin n → Fin V, ‖(nodeMask e A b).det‖ := norm_sum_le _ _
    _ ≤ ∑ _b : Fin n → Fin V, f θ := by
      apply sum_le_sum
      intro b _
      by_cases hn : (nodeMask e A b).det = 0
      · rw [hn,norm_zero]
        exact prod_nonneg fun _ _ => norm_nonneg _
      · obtain ⟨σ,hσ,_⟩ := nonzero_node_allocation e A b hn
        rw [allocation_norm_eq e A b σ hσ]
        exact hθ σ (mem_univ _)
    _ = _ := by simp [f,Fintype.card_fun]

end PiPolynomialValues.FourPeriod
