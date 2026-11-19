module

public import OddPiPowers.PolynomialValues.FourPeriod.RowOperator
public import OddPiPowers.PolynomialValues.FourPeriod.DeterminantDerivative
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! The Laurent determinant after a common frequency shift. The inner
indeterminate is y and the outer indeterminate is z. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

def shiftedFrequency (U : ℕ) (t : ℤ) : ℕ := (t + U).toNat

theorem derivative_rowOperator {A : Type*} [CommRing A] (s u : A) (r : ℕ) (p : A[X]) :
    (rowOperator s u r p).derivative = rowOperator s u r p.derivative := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [rowOperator, rowStep, derivative_add, derivative_C_mul, ih]

theorem rowOperator_zero {A : Type*} [CommRing A] (s u : A) (r : ℕ) :
    rowOperator s u r 0 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [rowOperator, rowStep, ih]

noncomputable def symbolEntry (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ) : Polynomial (ℂ[X]) :=
  ∑ t ∈ S, Polynomial.C ((X : ℂ[X]) ^ shiftedFrequency U t) *
    (rowOperator 1 (t : ℂ) r (Polynomial.derivative^[k] (p t))).map (Polynomial.C : ℂ →+* ℂ[X])

theorem derivative_symbolEntry (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ) :
    (symbolEntry S p U r k).derivative = symbolEntry S p U r (k + 1) := by
  simp only [symbolEntry, map_sum, derivative_C_mul, derivative_map, derivative_rowOperator,
    Function.iterate_succ_apply']

theorem symbolEntry_eq_zero_of_degree_lt (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ)
    (h : ∀ t ∈ S, (p t).natDegree < k) : symbolEntry S p U r k = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  rw [iterate_derivative_eq_zero (h t ht), rowOperator_zero, Polynomial.map_zero, mul_zero]

noncomputable def symbolMatrix (S : Finset ℤ) (p : ℤ → ℂ[X]) (U J : ℕ) :
    Matrix (Fin (J + 1)) (Fin (J + 1)) (Polynomial (ℂ[X])) :=
  Matrix.of fun r k => symbolEntry S p U r.val k.val

/-- The polynomial in y obtained by evaluating the symbol determinant at z = 0. -/
noncomputable def symbolPolynomial (S : Finset ℤ) (p : ℤ → ℂ[X]) (U J : ℕ) : ℂ[X] :=
  (symbolMatrix S p U J).det.coeff 0

theorem symbol_det_constant (S : Finset ℤ) (p : ℤ → ℂ[X]) (U J : ℕ)
    (hd : ∀ t ∈ S, (p t).natDegree ≤ J) :
    (symbolMatrix S p U J).det = C (symbolPolynomial S p U J) := by
  apply determinant_constant_of_shift
  · intro j i
    exact derivative_symbolEntry S p U i.val j.val
  · intro i
    change (symbolEntry S p U i.val J).derivative = 0
    rw [derivative_symbolEntry]
    exact symbolEntry_eq_zero_of_degree_lt S p U _ _ fun t ht => Nat.lt_succ_of_le (hd t ht)

end PiPolynomialValues.FourPeriod
