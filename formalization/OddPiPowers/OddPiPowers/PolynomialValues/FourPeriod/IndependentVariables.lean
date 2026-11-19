module

public import OddPiPowers.PolynomialValues.FourPeriod.VandermondeCollisions
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-! Each frequency column has its own variable. A coordinate derivative of
the determinant differentiates just that column, including for arbitrary
polynomials in that column. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset MvPolynomial

noncomputable def inCoordinate {n : ℕ} (i : Fin n) (f : Polynomial ℤ) : MvPolynomial (Fin n) ℤ :=
  f.eval₂ MvPolynomial.C (MvPolynomial.X i)

theorem pderiv_inCoordinate {n : ℕ} (i j : Fin n) (f : Polynomial ℤ) :
    pderiv i (inCoordinate j f) = if i=j then inCoordinate j f.derivative else 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have ea (u v : Polynomial ℤ) : inCoordinate j (u+v) = inCoordinate j u + inCoordinate j v :=
      Polynomial.eval₂_add _ _
    rw [ea, map_add, hf, hg, Polynomial.derivative_add, ea]
    split_ifs <;> simp
  | monomial m z =>
    by_cases hij : i=j
    · subst j
      simp only [inCoordinate, Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
        pderiv_C_mul, pderiv_pow, pderiv_X_self, mul_one, if_pos rfl, ite_true, map_mul, map_natCast]
      ring
    · simp only [inCoordinate, Polynomial.eval₂_monomial, pderiv_C_mul, pderiv_pow,
        pderiv_X_of_ne (Ne.symm hij), mul_zero, if_neg hij]

theorem eval_inCoordinate {n : ℕ} (x : Fin n → ℤ) (j : Fin n) (f : Polynomial ℤ) :
    MvPolynomial.eval x (inCoordinate j f) = f.eval (x j) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [inCoordinate, Polynomial.eval₂_add, map_add, Polynomial.eval_add]
      using congrArg₂ (·+·) hf hg
  | monomial m z => simp [inCoordinate, Polynomial.eval₂_monomial]

noncomputable def columnMatrix {n : ℕ} (P : Fin n → Fin n → Polynomial ℤ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℤ) :=
  Matrix.of (fun i j => inCoordinate j (P i j))

noncomputable def changeColumnDerivative {n : ℕ} (k : Fin n) (P : Fin n → Fin n → Polynomial ℤ)
    (i j : Fin n) : Polynomial ℤ := if j=k then (P i j).derivative else P i j

private theorem pderiv_prod_zero {n : ℕ} (k : Fin n) (S : Finset (Fin n))
    (f : Fin n → MvPolynomial (Fin n) ℤ) (h : ∀ j ∈ S, pderiv k (f j) = 0) :
    pderiv k (∏ j ∈ S, f j) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    rw [prod_insert hj, pderiv_mul, h j (by simp), ih (fun t ht => h t (mem_insert_of_mem ht))]
    simp

private theorem differentiate_permutation_term {n : ℕ} (k : Fin n)
    (P : Fin n → Fin n → Polynomial ℤ) (σ : Equiv.Perm (Fin n)) :
    pderiv k (∏ j, columnMatrix P (σ j) j) =
      ∏ j, columnMatrix (changeColumnDerivative k P) (σ j) j := by
  let S := (univ : Finset (Fin n)).erase k
  have hz : pderiv k (∏ j ∈ S, columnMatrix P (σ j) j) = 0 := by
    apply pderiv_prod_zero
    intro j hj
    change pderiv k (inCoordinate j (P (σ j) j)) = 0
    rw [pderiv_inCoordinate, if_neg (ne_of_mem_erase hj).symm]
  have hout : (∏ j ∈ S, columnMatrix (changeColumnDerivative k P) (σ j) j) =
      ∏ j ∈ S, columnMatrix P (σ j) j := by
    apply prod_congr rfl
    intro j hj
    simp only [columnMatrix, Matrix.of_apply, changeColumnDerivative, if_neg (ne_of_mem_erase hj)]
  rw [← Finset.prod_erase_mul univ (fun j => columnMatrix P (σ j) j) (mem_univ k),
    ← Finset.prod_erase_mul univ (fun j => columnMatrix (changeColumnDerivative k P) (σ j) j) (mem_univ k)]
  change pderiv k ((∏ j ∈ S, columnMatrix P (σ j) j) * inCoordinate k (P (σ k) k)) = _
  rw [pderiv_mul, hz, zero_mul, zero_add, pderiv_inCoordinate, if_pos rfl, hout]
  simp only [columnMatrix, Matrix.of_apply, changeColumnDerivative, if_pos rfl, ite_true]

theorem pderiv_columnMatrix_det {n : ℕ} (k : Fin n) (P : Fin n → Fin n → Polynomial ℤ) :
    pderiv k (columnMatrix P).det = (columnMatrix (changeColumnDerivative k P)).det := by
  classical
  simp only [Matrix.det_apply', map_sum, pderiv_mul, Derivation.map_intCast, zero_mul, zero_add]
  apply sum_congr rfl
  intro σ _
  rw [differentiate_permutation_term]

end PiPolynomialValues.FourPeriod
