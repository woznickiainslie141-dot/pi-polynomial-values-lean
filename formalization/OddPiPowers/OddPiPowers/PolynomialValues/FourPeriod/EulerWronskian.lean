module

public import OddPiPowers.PolynomialValues.FourPeriod.FirstCoefficients
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.LinearAlgebra.Vandermonde

/-! At distinct first orders, the first coefficient of the normalized Euler
derivative matrix is a Vandermonde matrix times a nonzero diagonal matrix. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PowerSeries

/-- Euler differentiation, applied to a formal series at the origin. -/
noncomputable def euler : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ :=
  (Algebra.lmul ℂ (PowerSeries ℂ) PowerSeries.X).comp PowerSeries.derivative.toLinearMap

theorem coeff_euler (p : PowerSeries ℂ) (n : ℕ) :
    coeff n (euler p) = (n : ℂ) * coeff n p := by
  change coeff n (X * PowerSeries.derivative p) = _
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have h := coeff_X_pow_mul (PowerSeries.derivative p) 1 n
    simpa only [pow_one, coeff_derivative, Nat.cast_succ, mul_comm] using h

theorem coeff_euler_pow (p : PowerSeries ℂ) (r n : ℕ) :
    coeff n ((euler ^ r) p) = (n : ℂ) ^ r * coeff n p := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', Module.End.mul_apply, coeff_euler, ih, pow_succ', mul_assoc]

private noncomputable def dropCoeffs (n : ℕ) (p : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => coeff (k + n) p)

private theorem dropCoeffs_mul_X (n : ℕ) (p : PowerSeries ℂ) (h : ∀ k < n, coeff k p = 0) :
    dropCoeffs n p * X ^ n = p := by
  ext k
  rw [mul_comm, coeff_X_pow_mul']
  by_cases hk : n ≤ k
  · simp only [hk, ite_true, dropCoeffs, coeff_mk, Nat.sub_add_cancel hk]
  · simp only [hk, ite_false, h k (Nat.lt_of_not_ge hk)]

noncomputable def eulerMatrix {n : ℕ} (p : Fin n → PowerSeries ℂ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
  Matrix.of (fun r i => (euler ^ (r : ℕ)) (p i))

theorem euler_det_ne_zero_of_first {n : ℕ} (p : Fin n → PowerSeries ℂ)
    (m : Fin n → ℕ) (hinj : Function.Injective m) (hm : ∀ i, FirstCoefficient (p i) (m i)) :
    (eulerMatrix p).det ≠ 0 := by
  classical
  let Q : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of (fun r i => dropCoeffs (m i) ((euler ^ (r : ℕ)) (p i)))
  let a (i : Fin n) := coeff (m i) (p i)
  let v (i : Fin n) := (m i : ℂ)
  have hQ : (PowerSeries.constantCoeff (R := ℂ)).mapMatrix Q =
      (Matrix.vandermonde v).transpose * Matrix.diagonal a := by
    ext r i
    change constantCoeff (dropCoeffs (m i) ((euler ^ (r : ℕ)) (p i))) = _
    rw [← coeff_zero_eq_constantCoeff_apply, dropCoeffs, coeff_mk, Nat.zero_add, coeff_euler_pow]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply, v, a]
  have hQdet : Q.det ≠ 0 := by
    intro hzero
    have h := (PowerSeries.constantCoeff (R := ℂ)).map_det Q
    rw [hzero, map_zero, hQ, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    exact (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr (Nat.cast_injective.comp hinj))
      (Finset.prod_ne_zero_iff.mpr fun i _ => (hm i).1)) h.symm
  have hM : eulerMatrix p = Q * Matrix.diagonal (fun i => (X : PowerSeries ℂ) ^ (m i)) := by
    apply Matrix.ext
    intro r i
    rw [Matrix.mul_diagonal]
    apply Eq.symm
    apply dropCoeffs_mul_X
    intro k hk
    change coeff k ((euler ^ (r : ℕ)) (p i)) = 0
    rw [coeff_euler_pow, (hm i).2 k hk, mul_zero]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hQdet (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ PowerSeries.X_ne_zero)

/-- A constant change of columns of the original family gives the echelon
family. Its nonzero Euler determinant forces the original determinant to be nonzero. -/
theorem euler_det_ne_zero {n : ℕ} (p : Fin n → PowerSeries ℂ) (hp : LinearIndependent ℂ p) :
    (eulerMatrix p).det ≠ 0 := by
  classical
  let F := Fintype.linearCombination ℂ p
  obtain ⟨x, m, hi, hm⟩ := exists_distinct_first_coefficients n F
    hp.fintypeLinearCombination_injective (by simp)
  let A : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of (fun j i => C (x i j))
  have hM : eulerMatrix (fun i => F (x i)) = eulerMatrix p * A := by
    apply Matrix.ext
    intro r i
    change (euler ^ (r : ℕ)) (Fintype.linearCombination ℂ p (x i)) = _
    rw [Fintype.linearCombination_apply, map_sum, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    change (euler ^ (r : ℕ)) (x i j • p j) = (euler ^ (r : ℕ)) (p j) * C (x i j)
    rw [(euler ^ (r : ℕ)).map_smul, PowerSeries.smul_eq_C_mul, mul_comm]
  have h := euler_det_ne_zero_of_first (fun i => F (x i)) m hi hm
  rw [hM, Matrix.det_mul] at h
  exact left_ne_zero_of_mul h

end PiPolynomialValues.FourPeriod
