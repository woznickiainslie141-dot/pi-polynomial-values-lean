module

public import OddPiPowers.PolynomialValues.FourPeriod.IndependentVariables

/-! A concrete integer determinant, with one complete prefix of monomials
and an arbitrary derivative order specified independently for each column. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open MvPolynomial

theorem iter_columnMatrix_det {n : ℕ} (ds : List (Fin n)) (P : Fin n → Fin n → Polynomial ℤ) :
    iterPartials coordinateDerivative ds (columnMatrix P).det =
      (columnMatrix (fun i j => (Polynomial.derivative^[ds.count j]) (P i j))).det := by
  induction ds generalizing P with
  | nil => simp [iterPartials]
  | cons k ds ih =>
    change iterPartials coordinateDerivative ds (pderiv k (columnMatrix P).det) = _
    rw [pderiv_columnMatrix_det, ih]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    apply congrArg (inCoordinate j)
    by_cases h : j=k
    · subst j
      simp [changeColumnDerivative, List.count_cons, Function.iterate_succ_apply]
    · simp [changeColumnDerivative, List.count_cons, h, Ne.symm h]

theorem integer_derivative_block_divisible {n : ℕ} (p : ℤ) (x : Fin n → ℤ) (ds : List (Fin n)) :
    p ^ (collidingPairs p x - ds.length) ∣
      (Matrix.of (fun i j : Fin n =>
        ((Polynomial.derivative^[ds.count j]) ((Polynomial.X : Polynomial ℤ)^i.val)).eval (x j))).det := by
  let P (_i j : Fin n) : Polynomial ℤ := Polynomial.X ^ j.val
  let A := Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))
  have hbase : columnMatrix (fun i j => P j i) = A.transpose := by
    ext i j
    simp [columnMatrix, inCoordinate, P, A, Matrix.vandermonde_apply]
  have he : MvPolynomial.eval x (iterPartials coordinateDerivative ds A.det) =
      (Matrix.of (fun i j : Fin n =>
        ((Polynomial.derivative^[ds.count j]) ((Polynomial.X : Polynomial ℤ)^i.val)).eval (x j))).det := by
    rw [← Matrix.det_transpose A, ← hbase, iter_columnMatrix_det, RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    exact eval_inCoordinate x j _
  rw [← he]
  exact prime_power_dvd_vandermonde_derivative p x ds

end PiPolynomialValues.FourPeriod
