module

public import OddPiPowers.PolynomialValues.FourPeriod.IntegerMatrix

/-! Factorial normalization of the four-period matrix in its complex specialization. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def normalizedRowPolynomial (σ : ℕ) : ℂ[X] :=
  C ((σ.factorial : ℂ)⁻¹) * X ^ σ

/-- The entry with row polynomial t^σ/σ! and with the stated column factor 2^j. -/
noncomputable def normalizedEntry (v t : ℤ) (σ j : ℕ) (y : ℂ) : ℂ :=
  (2 : ℂ) ^ j * Complex.I ^ (v * t) *
    (rowOperator 1 ((v : ℂ) * Complex.I * y / 2) j (normalizedRowPolynomial σ)).eval (t : ℂ)

theorem rawEntry_eq_factorial_mul (v t : ℤ) (σ j : ℕ) (y : ℂ) :
    (rawEntry v t σ j).eval₂ GaussianInt.toComplex y =
      (σ.factorial : ℂ) * normalizedEntry v t σ j y := by
  rw [rawEntry_evaluate, normalizedEntry, normalizedRowPolynomial, rowOperator_C_mul,
    eval_mul, eval_C]
  let u := (v : ℂ) * Complex.I * y / 2
  have hu : (v : ℂ) * Complex.I * y = 2 * u := by dsimp [u]; ring
  change Complex.I ^ (v * t) *
    (rowOperator 2 ((v : ℂ) * Complex.I * y) j (X ^ σ)).eval (t : ℂ) =
    (σ.factorial : ℂ) * ((2 ^ j * Complex.I ^ (v * t)) *
      ((σ.factorial : ℂ)⁻¹ * (rowOperator 1 u j (X ^ σ)).eval (t : ℂ)))
  rw [hu, rowOperator_scale, eval_mul, eval_C]
  have hfac : (σ.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero σ)
  field_simp

theorem rawDeterminant_evaluate {n : ℕ} (rows cols : Fin n → ℤ × ℕ) (y : ℂ) :
    (rawDeterminant rows cols).eval₂ GaussianInt.toComplex y =
      (∏ i, ((rows i).2.factorial : ℂ)) *
        (Matrix.of fun i j => normalizedEntry (rows i).1 (cols j).1 (rows i).2 (cols j).2 y).det := by
  let φ := eval₂RingHom GaussianInt.toComplex y
  change φ (Matrix.det (Matrix.of fun i j => rawEntry (rows i).1 (cols j).1 (rows i).2 (cols j).2)) = _
  rw [RingHom.map_det, ← Matrix.det_mul_column]
  congr 1
  ext i j
  exact rawEntry_eq_factorial_mul _ _ _ _ _

theorem rawDeterminant_eval_ne_zero_iff {n : ℕ} (rows cols : Fin n → ℤ × ℕ) (y : ℂ) :
    (rawDeterminant rows cols).eval₂ GaussianInt.toComplex y ≠ 0 ↔
      (Matrix.of fun i j => normalizedEntry (rows i).1 (cols j).1 (rows i).2 (cols j).2 y).det ≠ 0 := by
  rw [rawDeterminant_evaluate, mul_ne_zero_iff]
  exact and_iff_right (Finset.prod_ne_zero_iff.mpr fun i _ =>
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end PiPolynomialValues.FourPeriod
