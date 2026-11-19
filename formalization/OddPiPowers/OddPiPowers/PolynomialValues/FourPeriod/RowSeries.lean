module

public import OddPiPowers.PolynomialValues.FourPeriod.Normalization
public import OddPiPowers.PolynomialValues.FourPeriod.Symbol
public import OddPiPowers.PolynomialValues.FourPeriod.ExponentialIndependence

/-! Taylor coefficients on the exponential trajectory reproduce every row of
the factorial-normalized matrix at each signed frequency and node. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem derivative_normalizedRowPolynomial (σ : ℕ) :
    (normalizedRowPolynomial (σ + 1)).derivative = normalizedRowPolynomial σ := by
  rw [normalizedRowPolynomial, derivative_C_mul, derivative_X_pow, Nat.add_sub_cancel,
    ← mul_assoc, ← map_mul, normalizedRowPolynomial]
  have hs : ((σ + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hf : (σ.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  congr 2
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

theorem coeff_frequencyExp (t : ℂ) (σ : ℕ) :
    PowerSeries.coeff σ (frequencyExp t) = (normalizedRowPolynomial σ).eval t := by
  simp only [frequencyExp, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    normalizedRowPolynomial, eval_mul, eval_C, eval_pow, eval_X, map_div₀, map_one, map_natCast,
    one_div, map_inv₀, mul_comm]

/-- Coefficient of (w+u)^j exp(tw), with no approximation at any order. -/
theorem coeff_shifted_exponential (u t : ℂ) (j σ : ℕ) :
    PowerSeries.coeff σ ((PowerSeries.X + PowerSeries.C u) ^ j * frequencyExp t) =
      (rowOperator 1 u j (normalizedRowPolynomial σ)).eval t := by
  induction j generalizing σ with
  | zero => simpa [rowOperator] using coeff_frequencyExp t σ
  | succ j ih =>
    rw [pow_succ', mul_assoc, add_mul, map_add, PowerSeries.coeff_C_mul, ih,
      rowOperator, rowStep, map_one, one_mul, eval_add, eval_mul, eval_C, derivative_rowOperator]
    congr 1
    cases σ with
    | zero => simp [normalizedRowPolynomial, PowerSeries.coeff_zero_eq_constantCoeff_apply, rowOperator_zero]
    | succ k =>
      rw [derivative_normalizedRowPolynomial, ← ih k]
      simpa only [pow_one] using PowerSeries.coeff_X_pow_mul
        ((PowerSeries.X + PowerSeries.C u) ^ j * frequencyExp t) 1 k

noncomputable def entrySeries (v t : ℤ) (j : ℕ) (y : ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((2 : ℂ) ^ j * Complex.I ^ (v * t)) *
    ((PowerSeries.X + PowerSeries.C ((v : ℂ) * Complex.I * y / 2)) ^ j * frequencyExp (t : ℂ))

theorem coeff_entrySeries (v t : ℤ) (j σ : ℕ) (y : ℂ) :
    PowerSeries.coeff σ (entrySeries v t j y) = normalizedEntry v t σ j y := by
  rw [entrySeries, PowerSeries.coeff_C_mul, coeff_shifted_exponential, normalizedEntry]

theorem vanishing_prefix_iff (v : ℤ) (y : ℂ) (S : Finset (ℤ × ℕ))
    (a : ℤ × ℕ → ℂ) (h : ℕ) :
    (∀ σ < h, ∑ c ∈ S, a c * normalizedEntry v c.1 σ c.2 y = 0) ↔
      (PowerSeries.X : PowerSeries ℂ) ^ h ∣
        ∑ c ∈ S, PowerSeries.C (a c) * entrySeries v c.1 c.2 y := by
  rw [PowerSeries.X_pow_dvd_iff]
  simp only [map_sum, PowerSeries.coeff_C_mul, coeff_entrySeries]

end PiPolynomialValues.FourPeriod
