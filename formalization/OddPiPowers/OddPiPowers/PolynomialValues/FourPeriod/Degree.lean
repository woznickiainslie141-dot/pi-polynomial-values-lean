module

public import OddPiPowers.PolynomialValues.FourPeriod.IntegerMatrix
public import Mathlib.Algebra.Polynomial.BigOperators

/-! Column degrees of the integral monomial matrix. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

private theorem nodeCoefficient_degree (v : ℤ) : (nodeCoefficient v).natDegree ≤ 1 := by
  unfold nodeCoefficient
  exact (natDegree_mul_le ..).trans (by rw [natDegree_C, natDegree_X, Nat.zero_add])

private theorem rawCoefficient_degree (v : ℤ) (σ j i : ℕ) :
    ((rowOperator (2 : GaussianInt[X]) (nodeCoefficient v) j (X ^ σ)).coeff i).natDegree ≤ j := by
  induction j generalizing i with
  | zero =>
    simp only [rowOperator, coeff_X_pow]
    split <;> simp
  | succ j ih =>
    rw [rowOperator, rowStep, coeff_add, coeff_C_mul, coeff_C_mul, coeff_derivative]
    apply natDegree_add_le_of_degree_le
    · apply (natDegree_mul_le ..).trans
      rw [natDegree_ofNat]
      apply (Nat.zero_add _).le.trans
      apply (natDegree_mul_le ..).trans
      rw [← Nat.cast_succ, natDegree_natCast, Nat.add_zero]
      exact (ih _).trans (Nat.le_succ j)
    · exact (natDegree_mul_le ..).trans (by have := nodeCoefficient_degree v; have := ih i; omega)

theorem rawEntry_degree (v t : ℤ) (σ j : ℕ) : (rawEntry v t σ j).natDegree ≤ j := by
  unfold rawEntry
  apply (natDegree_mul_le ..).trans
  rw [natDegree_C, Nat.zero_add, eval_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_mul_le ..).trans
  rw [← map_pow, natDegree_C, Nat.add_zero]
  exact rawCoefficient_degree v σ j i

theorem rawDeterminant_degree {n : ℕ} (rows cols : Fin n → ℤ × ℕ) :
    (rawDeterminant rows cols).natDegree ≤ ∑ j, (cols j).2 := by
  unfold rawDeterminant
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro τ _
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le Finset.univ _).trans
  exact Finset.sum_le_sum fun j _ => rawEntry_degree _ _ _ _

end PiPolynomialValues.FourPeriod
