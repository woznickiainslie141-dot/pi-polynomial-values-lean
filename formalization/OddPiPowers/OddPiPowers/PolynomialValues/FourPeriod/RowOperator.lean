module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-! Polynomial identities for the scaled operator s times differentiation plus u. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

variable {A : Type*} [CommRing A]

noncomputable def rowStep (s u : A) (p : A[X]) : A[X] := C s * p.derivative + C u * p

noncomputable def rowOperator (s u : A) : ℕ → A[X] → A[X]
  | 0, p => p
  | j + 1, p => rowStep s u (rowOperator s u j p)

theorem rowStep_add (s u : A) (p q : A[X]) :
    rowStep s u (p + q) = rowStep s u p + rowStep s u q := by
  simp only [rowStep, derivative_add]
  ring

theorem rowStep_C_mul (s u a : A) (p : A[X]) :
    rowStep s u (C a * p) = C a * rowStep s u p := by
  rw [rowStep, derivative_C_mul, rowStep]
  ring

theorem rowStep_X_mul (s u : A) (p : A[X]) :
    rowStep s u (X * p) = X * rowStep s u p + C s * p := by
  simp only [rowStep, derivative_mul, derivative_X, one_mul]
  ring

theorem rowOperator_C_mul (s u a : A) (j : ℕ) (p : A[X]) :
    rowOperator s u j (C a * p) = C a * rowOperator s u j p := by
  induction j with
  | zero => rfl
  | succ j ih => rw [rowOperator, ih, rowStep_C_mul]; rfl

/-- Multiplication of a row polynomial by the frequency variable shifts every
layer by the same triangular rule at every node. -/
theorem rowOperator_X_mul_succ (s u : A) (j : ℕ) (p : A[X]) :
    rowOperator s u (j + 1) (X * p) =
      X * rowOperator s u (j + 1) p + C (((j + 1 : ℕ) : A) * s) * rowOperator s u j p := by
  induction j with
  | zero => simpa only [Nat.zero_add, rowOperator, Nat.cast_one, one_mul] using rowStep_X_mul s u p
  | succ j ih =>
    rw [rowOperator, ih, rowStep_add, rowStep_X_mul, rowStep_C_mul]
    change X * rowOperator s u (j + 2) p + C s * rowOperator s u (j + 1) p +
        C ((j + 1 : ℕ) * s) * rowOperator s u (j + 1) p = _
    simp only [Nat.cast_succ, map_add, map_mul, map_one]
    ring

/-- Scaling both terms of the operator multiplies the j-th iterate by s^j. -/
theorem rowOperator_scale (s u : A) (j : ℕ) (p : A[X]) :
    rowOperator s (s * u) j p = C (s ^ j) * rowOperator 1 u j p := by
  induction j with
  | zero => simp [rowOperator]
  | succ j ih =>
    rw [rowOperator, ih, rowStep_C_mul, rowOperator]
    simp only [rowStep, pow_succ, map_mul, map_one, one_mul]
    ring

/-- Ring maps commute with all row operations, including specialization of Y. -/
theorem map_rowOperator {B : Type*} [CommRing B] (φ : A →+* B)
    (s u : A) (j : ℕ) (p : A[X]) :
    (rowOperator s u j p).map φ = rowOperator (φ s) (φ u) j (p.map φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [rowOperator, rowStep, Polynomial.map_add, Polynomial.map_mul, map_C,
      ← derivative_map, ih]

end PiPolynomialValues.FourPeriod
