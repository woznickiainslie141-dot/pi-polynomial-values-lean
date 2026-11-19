module

public import OddPiPowers.PolynomialValues.FourPeriod.RowOperator
public import OddPiPowers.Foundations.GaussianArithmetic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The four-period matrix with monomial rows, before division by the row factorials. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial OddPiPowers

/-- The fourth-root-of-unity phase, also at negative integer frequencies. -/
def phase (k : ℤ) : GaussianInt := gaussianI ^ (k % 4).toNat

theorem phase_toComplex (k : ℤ) : GaussianInt.toComplex (phase k) = Complex.I ^ k := by
  rw [phase, map_pow, show GaussianInt.toComplex gaussianI = Complex.I from gaussianI_toComplex,
    Complex.I_zpow_eq_zpow_mod k, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]

/-- The operator acts in the frequency variable. Its coefficients are Gaussian
integer polynomials in the argument Y of the auxiliary determinant. -/
noncomputable def nodeCoefficient (v : ℤ) : GaussianInt[X] := C ((v : GaussianInt) * gaussianI) * X

noncomputable def rawEntry (v t : ℤ) (σ j : ℕ) : GaussianInt[X] :=
  C (phase (v * t)) *
    (rowOperator (2 : GaussianInt[X]) (nodeCoefficient v) j (X ^ σ)).eval (C (t : GaussianInt))

theorem rawEntry_shift_zero (v t : ℤ) (σ : ℕ) :
    rawEntry v t (σ + 1) 0 = C (t : GaussianInt) * rawEntry v t σ 0 := by
  simp only [rawEntry, rowOperator, eval_pow, eval_X, pow_succ, eval_mul]
  ring

theorem rawEntry_shift_succ (v t : ℤ) (σ j : ℕ) :
    rawEntry v t (σ + 1) (j + 1) = C (t : GaussianInt) * rawEntry v t σ (j + 1) +
      (((j + 1 : ℕ) : GaussianInt[X]) * 2) * rawEntry v t σ j := by
  simp only [rawEntry, pow_succ' (X : (GaussianInt[X])[X]) σ, rowOperator_X_mul_succ,
    eval_add, eval_mul, eval_X, eval_C]
  ring

/-- A square auxiliary determinant over the Gaussian integers, for any concrete
ordered list of nodes and orders and any ordered list of frequencies and layers. -/
noncomputable def rawDeterminant {n : ℕ} (rows cols : Fin n → ℤ × ℕ) : GaussianInt[X] :=
  (Matrix.of fun i j => rawEntry (rows i).1 (cols j).1 (rows i).2 (cols j).2).det

/-- Specializing the actual polynomial reproduces the differential matrix
entry with the same phase at the actual signed frequency. -/
theorem rawEntry_evaluate (v t : ℤ) (σ j : ℕ) (y : ℂ) :
    (rawEntry v t σ j).eval₂ GaussianInt.toComplex y =
      Complex.I ^ (v * t) * (rowOperator (2 : ℂ) ((v : ℂ) * Complex.I * y) j (X ^ σ)).eval (t : ℂ) := by
  let φ := eval₂RingHom GaussianInt.toComplex y
  have hu : φ (nodeCoefficient v) = (v : ℂ) * Complex.I * y := by
    simp only [φ, nodeCoefficient, coe_eval₂RingHom, eval₂_C, eval₂_X,
      map_mul, map_intCast, show GaussianInt.toComplex gaussianI = Complex.I from gaussianI_toComplex]
  have ht : φ (C (t : GaussianInt)) = (t : ℂ) := by
    simp only [φ, map_intCast]
  rw [rawEntry, eval₂_mul, eval₂_C, phase_toComplex]
  congr 1
  change φ ((rowOperator _ _ j (X ^ σ)).eval (C (t : GaussianInt))) = _
  rw [← eval_map_apply, map_rowOperator, ht, hu, map_ofNat, Polynomial.map_pow, map_X]

end PiPolynomialValues.FourPeriod
