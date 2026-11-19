module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Differentiate a polynomial determinant one column at a time. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem derivative_determinant (A : Matrix ι ι R[X]) :
    A.det.derivative = ∑ j, (A.updateCol j (fun i => (A i j).derivative)).det := by
  classical
  simp only [Matrix.det_apply', map_sum, derivative_intCast_mul, derivative_prod_finset,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => A.updateCol j (fun k => (A k j).derivative) (σ i) i) (Finset.mem_univ j),
    Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]

/-- Shifting each differentiated column to its successor (and killing the last)
forces the determinant to be a constant in the coefficient ring. -/
theorem determinant_constant_of_shift [IsDomain R] [CharZero R] {J : ℕ}
    (A : Matrix (Fin (J + 1)) (Fin (J + 1)) R[X])
    (hstep : ∀ j : Fin J, ∀ i, (A i j.castSucc).derivative = A i j.succ)
    (hlast : ∀ i, (A i (Fin.last J)).derivative = 0) :
    A.det = C (A.det.coeff 0) := by
  apply eq_C_of_derivative_eq_zero
  rw [derivative_determinant]
  apply Finset.sum_eq_zero
  intro j _
  refine Fin.lastCases (motive := fun k => (A.updateCol k (fun i => (A i k).derivative)).det = 0)
    ?_ (fun j => ?_) j
  · exact Matrix.det_eq_zero_of_column_eq_zero (Fin.last J)
      (fun i => by rw [Matrix.updateCol_self]; exact hlast i)
  ·
    have h : (fun i => (A i j.castSucc).derivative) = (fun i => A i j.succ) :=
      funext (hstep j)
    rw [h]
    apply Matrix.det_updateCol_eq_zero
    exact fun he => (Nat.succ_ne_self j.val) (congrArg Fin.val he)

end PiPolynomialValues.FourPeriod
