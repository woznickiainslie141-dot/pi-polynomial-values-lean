module

public import OddPiPowers.PolynomialValues.FourPeriod.Wronskian
public import Mathlib.RingTheory.PowerSeries.Order

/-! Vanishing orders of simultaneous constant combinations of the Wronskian
columns at one base point. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PowerSeries

theorem derivative_prefix_dvd (f : PowerSeries ℂ) (h J r : ℕ) (hr : r ≤ J)
    (hf : (X : PowerSeries ℂ) ^ h ∣ f) :
    (X : PowerSeries ℂ) ^ (h - J) ∣ PowerSeries.derivative^[r] f := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  rw [coeff_iterate_derivative, X_pow_dvd_iff.mp hf (k + r) (by omega), mul_zero]

theorem wronskian_prefix_dvd {J : ℕ} (f : Fin (J + 1) → PowerSeries ℂ)
    (h : Fin (J + 1) → ℕ) (hf : ∀ i, X ^ h i ∣ f i) :
    X ^ (∑ i, (h i - J)) ∣ (wronskianMatrix f).det := by
  classical
  have he (r i : Fin (J + 1)) : X ^ (h i - J) ∣ wronskianMatrix f r i :=
    derivative_prefix_dvd _ _ _ _ (Nat.le_of_lt_succ r.isLt) (hf i)
  choose q hq using he
  let Q := Matrix.of q
  have hM : wronskianMatrix f = Q * Matrix.diagonal (fun i => X ^ (h i - J)) := by
    apply Matrix.ext
    intro r i
    rw [Matrix.mul_diagonal]
    exact (hq r i).trans (mul_comm ..)
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_left _ _

noncomputable def mixColumn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → PowerSeries ℂ) (i : Fin n) : PowerSeries ℂ := ∑ k, B k i • f k

theorem wronskian_change_columns {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → PowerSeries ℂ) :
    wronskianMatrix (mixColumn B f) = wronskianMatrix f * (C : ℂ →+* PowerSeries ℂ).mapMatrix B := by
  apply Matrix.ext
  intro r i
  let D : Module.End ℂ (PowerSeries ℂ) := PowerSeries.derivative.toLinearMap
  change D^[(r : ℕ)] (∑ k, B k i • f k) = _
  rw [← Module.End.pow_apply, map_sum, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [(D ^ (r : ℕ)).map_smul, Module.End.pow_apply, PowerSeries.smul_eq_C_mul, mul_comm]
  rfl

/-- If one constant nonsingular change of columns realizes the prescribed
vanishing at all chosen nodes, their losses in the Wronskian add. -/
theorem wronskian_order_of_combinations {J : ℕ} (f : Fin (J + 1) → PowerSeries ℂ)
    (B : Matrix (Fin (J + 1)) (Fin (J + 1)) ℂ) (hB : B.det ≠ 0)
    (h : Fin (J + 1) → ℕ) (hf : ∀ i, X ^ h i ∣ mixColumn B f i) :
    (↑(∑ i, (h i - J)) : ℕ∞) ≤ (wronskianMatrix f).det.order := by
  have hd := wronskian_prefix_dvd _ h hf
  have ho := nat_le_order_iff.mpr (X_pow_dvd_iff.mp hd)
  rw [wronskian_change_columns, Matrix.det_mul, ← RingHom.map_det, order_mul] at ho
  have hunit : IsUnit (PowerSeries.C B.det) := (isUnit_iff_ne_zero.mpr hB).map _
  rwa [order_zero_of_isUnit hunit, add_zero] at ho

noncomputable def translationMatrix {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k i => x i ^ (k : ℕ) / (k.val.factorial : ℂ)

theorem translationMatrix_det_ne_zero {n : ℕ} (x : Fin n → ℂ) (hx : Function.Injective x) :
    (translationMatrix x).det ≠ 0 := by
  have h : translationMatrix x = Matrix.diagonal (fun k : Fin n => (k.val.factorial : ℂ)⁻¹) *
      (Matrix.vandermonde x).transpose := by
    apply Matrix.ext
    intro k i
    simp only [translationMatrix, Matrix.of_apply, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.vandermonde_apply, div_eq_mul_inv, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ =>
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
    (Matrix.det_vandermonde_ne_zero_iff.mpr hx)

end PiPolynomialValues.FourPeriod
