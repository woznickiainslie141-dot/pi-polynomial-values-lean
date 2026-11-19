module

public import OddPiPowers.PolynomialValues.FourPeriod.EulerWronskian
public import Mathlib.Combinatorics.Enumerative.Stirling

/-! Nonvanishing of the ordinary Wronskian of linearly independent formal series. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PowerSeries

private theorem coeff_weighted_derivative (p : PowerSeries ℂ) (j k : ℕ) :
    coeff k (X ^ j * (PowerSeries.derivative^[j] p)) =
      (k.descFactorial j : ℂ) * coeff k p := by
  rw [coeff_X_pow_mul']
  by_cases hj : j ≤ k
  · simp only [hj, ite_true, coeff_iterate_derivative, ← Nat.add_descFactorial_eq_ascFactorial,
      Nat.sub_add_cancel hj]
  · simp only [hj, ite_false, Nat.descFactorial_of_lt (Nat.lt_of_not_ge hj), Nat.cast_zero, zero_mul]

private theorem stirling_sum_fin {n : ℕ} (r : Fin n) (k : ℕ) :
    k ^ r.val = ∑ j : Fin n, r.val.stirlingSecond j.val * k.descFactorial j.val := by
  calc
    _ = ∑ j ∈ Finset.range n, r.val.stirlingSecond j * k.descFactorial j := by
      rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
      apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono r.isLt)
      · intro j hj
        have hj₁ := Finset.mem_sdiff.mp hj
        have hlt : (r : ℕ) < j := by simpa using hj₁.2
        rw [Nat.stirlingSecond_eq_zero_of_lt hlt, zero_mul]
      · intro _ _; rfl
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun j => r.val.stirlingSecond j * k.descFactorial j) n).symm

private theorem euler_as_derivatives {n : ℕ} (r : Fin n) (p : PowerSeries ℂ) :
    (euler ^ (r : ℕ)) p =
      ∑ j : Fin n, C (r.val.stirlingSecond (j : ℕ) : ℂ) *
        (X ^ (j : ℕ) * PowerSeries.derivative^[(j : ℕ)] p) := by
  ext k
  rw [coeff_euler_pow, map_sum]
  simp only [coeff_C_mul, coeff_weighted_derivative]
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun m : ℕ => (m : ℂ)) (stirling_sum_fin r k)

noncomputable def wronskianMatrix {n : ℕ} (p : Fin n → PowerSeries ℂ) :
    Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
  Matrix.of (fun r i => PowerSeries.derivative^[(r : ℕ)] (p i))

/-- Ordinary derivatives suffice, including when some input has nonzero
constant coefficient. -/
theorem wronskian_det_ne_zero {n : ℕ} (p : Fin n → PowerSeries ℂ) (hp : LinearIndependent ℂ p) :
    (wronskianMatrix p).det ≠ 0 := by
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of (fun r j => C (r.val.stirlingSecond (j : ℕ) : ℂ) * X ^ (j : ℕ))
  have h : eulerMatrix p = B * wronskianMatrix p := by
    apply Matrix.ext
    intro r i
    simpa only [eulerMatrix, wronskianMatrix, B, Matrix.of_apply, Matrix.mul_apply, mul_assoc] using
      euler_as_derivatives r (p i)
  have hn := euler_det_ne_zero p hp
  rw [h, Matrix.det_mul] at hn
  exact right_ne_zero_of_mul hn

end PiPolynomialValues.FourPeriod
