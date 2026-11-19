module

public import OddPiPowers.PolynomialValues.Analysis.ColumnBlockNorm
public import OddPiPowers.PolynomialValues.Analysis.NodeAllocationNorm

/-! Size of a complete normalized minor, with row factorials and column
amplitudes kept separate for the empirical energy estimate. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

noncomputable def pathBlock {n : ℕ} (x : Fin n → ℤ) (j : Fin n → ℕ) (z c : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i l =>
    c l * (rowOperator 1 (z l) (j l) (normalizedRowPolynomial i.val)).eval (x l : ℂ)

noncomputable def factorialWeight (n : ℕ) : ℝ := ∏ i : Fin n, (i.val.factorial : ℝ)⁻¹

theorem pathBlock_bound {n : ℕ} (x : Fin n → ℤ) (j : Fin n → ℕ) (z c : Fin n → ℂ) :
    ‖(pathBlock x j z c).det‖ ≤ factorialWeight n*(∏ i, ‖c i‖)*
      (pairEnvelope x*∏ i, (‖z i‖ + blockGrowth n)^j i) := by
  let d (i : Fin n) := (i.val.factorial : ℂ)⁻¹
  let A := shiftedBlock x j z
  let B := Matrix.of (fun i l => c l*A i l)
  have he : pathBlock x j z c = Matrix.of (fun i l => d i*B i l) := by
    ext i l
    simp only [pathBlock,normalizedRowPolynomial,rowOperator_C_mul,eval_mul,eval_C,
      Matrix.of_apply,B,A,shiftedBlock,d]
    ring
  rw [he,Matrix.det_mul_column,show B.det = (∏ i, c i)*A.det from Matrix.det_mul_row c A,
    norm_mul,norm_mul,norm_prod,norm_prod]
  simp only [d,norm_inv,Complex.norm_natCast]
  change factorialWeight n*((∏ i, ‖c i‖)*‖A.det‖) ≤ _
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left (shiftedBlock_bound x j z)
  exact mul_nonneg (prod_nonneg (fun _ _ => by positivity)) (prod_nonneg (fun _ _ => norm_nonneg _))

noncomputable def pathMatrix {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (x : Fin n → ℤ) (j : Fin n → ℕ) (z c : Fin V → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i l => c (e i).1 l *
    (rowOperator 1 (z (e i).1 l) (j l) (normalizedRowPolynomial (e i).2.val)).eval (x l : ℂ)

def allocatedColumn {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (θ : Equiv.Perm (Fin n)) (v : Fin V) (i : Fin (m v)) : Fin n := θ.symm (e.symm ⟨v,i⟩)

theorem pathMatrix_bound {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (x : Fin n → ℤ) (j : Fin n → ℕ) (z c : Fin V → Fin n → ℂ) :
    ∃ θ : Equiv.Perm (Fin n), ‖(pathMatrix e x j z c).det‖ ≤ (V : ℝ)^n*
      ∏ v, (factorialWeight (m v)*(∏ i, ‖c v (allocatedColumn e θ v i)‖)*
        (pairEnvelope (x ∘ allocatedColumn e θ v)*
        ∏ i, (‖z v (allocatedColumn e θ v i)‖+blockGrowth (m v))^j (allocatedColumn e θ v i))) := by
  obtain ⟨θ,hθ⟩ := exists_node_norm_bound e (pathMatrix e x j z c)
  refine ⟨θ,hθ.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro v _
  let d := allocatedColumn e θ v
  have he : allocationBlock e (pathMatrix e x j z c) θ v =
      pathBlock (x ∘ d) (j ∘ d) (z v ∘ d) (c v ∘ d) := by
    ext i l
    simp only [allocationBlock,pathMatrix,pathBlock,Matrix.of_apply,e.apply_symm_apply,
      Function.comp_apply,d,allocatedColumn]
    rw [show (e (e.symm ⟨v,i⟩)).2.val = i.val from
      congrArg (fun p : RowCandidates m => p.2.val) (e.apply_symm_apply ⟨v,i⟩)]
  rw [he]
  exact pathBlock_bound _ _ _ _

end PiPolynomialValues.FourPeriod
