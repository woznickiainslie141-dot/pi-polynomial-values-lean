module

public import OddPiPowers.PolynomialValues.FourPeriod.IntegerMatrix
public import Mathlib.Algebra.Polynomial.BigOperators

/-! Extract a particular coefficient after expanding the determinant in
the powers of each column. The retained indices have exactly that sum. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

noncomputable def columnCoefficientMatrix {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R[X]) (h : Fin n → ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A i j).coeff (h j)

theorem det_column_expansion {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R[X])
    (L : ℕ) (hdeg : ∀ i j, (A i j).natDegree < L) :
    A.det = ∑ h : Fin n → Fin L, C (columnCoefficientMatrix A (fun j => (h j).val)).det *
      X^(∑ j, (h j).val) := by
  classical
  let D := (Matrix.detRowAlternating (n := Fin n) (R := R[X])).toMultilinearMap
  let line (j : Fin n) (k : Fin L) (i : Fin n) := C ((A i j).coeff k.val)
  let scalar (k : Fin L) := (X : R[X])^k.val
  have he : A.transpose.det = D (fun j => ∑ k, scalar k • line j k) := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro j i
    have hh := (A i j).as_sum_range_C_mul_X_pow' (hdeg i j)
    rw [← Fin.sum_univ_eq_sum_range] at hh
    simpa only [scalar,line,Matrix.transpose_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      mul_comm] using hh
  rw [← Matrix.det_transpose A,he,D.map_sum]
  apply sum_congr rfl
  intro h _
  rw [D.map_smul_univ,smul_eq_mul]
  have hd : D (fun j => line j (h j)) =
      C (columnCoefficientMatrix A (fun j => (h j).val)).det := by
    rw [RingHom.map_det,← Matrix.det_transpose]
    rfl
  rw [hd]
  simp only [scalar,prod_pow_eq_pow_sum,mul_comm]

theorem coeff_det_column_sum {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R[X])
    (L : ℕ) (hdeg : ∀ i j, (A i j).natDegree < L) (H : ℕ) :
    A.det.coeff H = ∑ h : Fin n → Fin L, if (∑ j, (h j).val) = H then
      (columnCoefficientMatrix A (fun j => (h j).val)).det else 0 := by
  rw [det_column_expansion A L hdeg,finsetSum_coeff]
  apply sum_congr rfl
  intro h _
  rw [coeff_C_mul_X_pow]
  split_ifs <;> simp_all

theorem C_dvd_quotient_of_column_terms {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R[X])
    (L : ℕ) (hdeg : ∀ i j, (A i j).natDegree < L) (k : ℕ) (q : R[X]) (hd : A.det = X^k*q) (g : R)
    (hg : ∀ h : Fin n → Fin L, k ≤ ∑ j, (h j).val → g ∣ (columnCoefficientMatrix A (fun j => (h j).val)).det) :
    C g ∣ q := by
  apply (C_dvd_iff_dvd_coeff g q).mpr
  intro s
  rw [← coeff_X_pow_mul q k s,← hd,coeff_det_column_sum A L hdeg]
  apply Finset.dvd_sum
  intro h _
  split_ifs with he
  · exact hg h (by omega)
  · exact dvd_zero _

end PiPolynomialValues.FourPeriod
