module

public import OddPiPowers.PolynomialValues.FourPeriod.ColumnPolynomials
public import OddPiPowers.PolynomialValues.FourPeriod.RowSeries
public import OddPiPowers.PolynomialValues.FourPeriod.Translation

/-! Turn an actual linear relation on the signed interpolation columns into
the vanishing hypotheses for the local contact budget. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem taylor_ofFn_series {n : ℕ} (c : Fin n → ℂ) (b : ℂ) :
    ((Polynomial.taylor b (Polynomial.ofFn n c) : ℂ[X]) : PowerSeries ℂ) =
      ∑ j, PowerSeries.C (c j) * (PowerSeries.X+PowerSeries.C b)^j.val := by
  change Polynomial.coeToPowerSeries.ringHom (Polynomial.taylor b (Polynomial.ofFn n c)) = _
  rw [Polynomial.ofFn_eq_sum_monomial, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.taylor_monomial, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]

theorem sum_actual_columns {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ)
    (S : Finset ℤ) (hS : ∀ j, Finset.Icc (-(U j : ℤ)) (U j : ℤ) ⊆ S)
    (f : ℤ → Fin n → PowerSeries ℂ) :
    ∑ t ∈ S, ∑ j, PowerSeries.C (layerCoefficient U a t j)* f t j =
      ∑ c : Column U, PowerSeries.C (2^c.1.val*a c) * f c.2.val c.1 := by
  classical
  rw [Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  let I := Finset.Icc (-(U j : ℤ)) (U j : ℤ)
  calc
    _ = ∑ t ∈ I, PowerSeries.C (layerCoefficient U a t j)*f t j := by
      symm
      apply Finset.sum_subset (hS j)
      intro t _ ht
      have hout : t ∉ Finset.Icc (-(U j : ℤ)) (U j : ℤ) := ht
      rw [layerCoefficient, dif_neg hout, map_zero, zero_mul]
    _ = ∑ t : ↥I, PowerSeries.C (layerCoefficient U a t.val j)*f t.val j :=
      (I.sum_coe_sort _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      dsimp only
      rw [layerCoefficient, dif_pos t.property]

theorem translatedTrajectory_eq_entrySeries {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ)
    (S : Finset ℤ) (hS : ∀ j, Finset.Icc (-(U j : ℤ)) (U j : ℤ) ⊆ S)
    (v : ℤ) (y : ℂ) :
    translatedTrajectory (Complex.I^v) ((v : ℂ)*Complex.I*y/2) S (columnPolynomial U a) =
      ∑ c : Column U, PowerSeries.C (a c)*entrySeries v c.2.val c.1.val y := by
  let b : ℂ := (v : ℂ)*Complex.I*y/2
  let f (t : ℤ) (j : Fin n) : PowerSeries ℂ :=
    PowerSeries.C ((Complex.I^v)^t)*(frequencyExp (t : ℂ)*(PowerSeries.X+PowerSeries.C b)^j.val)
  calc
    _ = ∑ t ∈ S, ∑ j, PowerSeries.C (layerCoefficient U a t j)*f t j := by
      unfold translatedTrajectory
      apply Finset.sum_congr rfl
      intro t _
      rw [columnPolynomial, taylor_ofFn_series, PowerSeries.smul_eq_C_mul,
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f,b]
      ring
    _ = _ := by
      rw [sum_actual_columns U a S hS f]
      apply Finset.sum_congr rfl
      intro c _
      simp only [f, b, entrySeries, ← zpow_mul, map_mul]
      ring

theorem translatedTrajectory_prefix_dvd {n : ℕ} (U : Fin n → ℕ) (a : Column U → ℂ)
    (S : Finset ℤ) (hS : ∀ j, Finset.Icc (-(U j : ℤ)) (U j : ℤ) ⊆ S)
    (v : ℤ) (y : ℂ) (h : ℕ)
    (hr : ∀ σ < h, ∑ c : Column U, a c * normalizedEntry v c.2.val σ c.1.val y = 0) :
    (PowerSeries.X : PowerSeries ℂ)^h ∣
      translatedTrajectory (Complex.I^v) ((v : ℂ)*Complex.I*y/2) S (columnPolynomial U a) := by
  rw [translatedTrajectory_eq_entrySeries U a S hS v y, PowerSeries.X_pow_dvd_iff]
  intro σ hσ
  simpa only [map_sum, PowerSeries.coeff_C_mul, coeff_entrySeries] using hr σ hσ

end PiPolynomialValues.FourPeriod
