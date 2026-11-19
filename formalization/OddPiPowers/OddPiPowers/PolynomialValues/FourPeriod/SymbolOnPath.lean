module

public import OddPiPowers.PolynomialValues.FourPeriod.Symbol
public import OddPiPowers.PolynomialValues.FourPeriod.TrajectoryColumns
public import OddPiPowers.PolynomialValues.FourPeriod.Wronskian

/-! The polynomial symbol has a nonzero specialized determinant on the
formal path y = exp(w), z = w. This proves the symbol itself is nonzero. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem derivative_frequency_mul_row (t : ℂ) (p : ℂ[X]) (r : ℕ) :
    PowerSeries.derivative^[r] (frequencyExp t * (p : PowerSeries ℂ)) =
      frequencyExp t * ((rowOperator 1 t r p : ℂ[X]) : PowerSeries ℂ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, PowerSeries.derivative.leibniz,
      PowerSeries.derivative_coe, derivative_frequencyExp]
    simp only [rowOperator, rowStep, map_one, one_mul, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_C, smul_eq_mul]
    ring

theorem derivative_trajectoryColumn (S : Finset ℤ) (p : ℤ → ℂ[X]) (r k : ℕ) :
    PowerSeries.derivative^[r] (trajectoryColumn S p k) =
      ∑ t ∈ S, frequencyExp (t : ℂ) *
        ((rowOperator 1 (t : ℂ) r (Polynomial.derivative^[k] (p t)) : ℂ[X]) : PowerSeries ℂ) := by
  let D : Module.End ℂ (PowerSeries ℂ) := PowerSeries.derivative.toLinearMap
  change D^[r] (∑ t ∈ S, _) = _
  rw [← Module.End.pow_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Module.End.pow_apply]
  exact derivative_frequency_mul_row (t : ℂ) _ r

noncomputable def symbolOnPath : Polynomial (ℂ[X]) →+* PowerSeries ℂ :=
  eval₂RingHom (eval₂RingHom (PowerSeries.C : ℂ →+* PowerSeries ℂ) (PowerSeries.exp ℂ)) PowerSeries.X

theorem symbolEntry_on_path (S : Finset ℤ) (p : ℤ → ℂ[X]) (U r k : ℕ)
    (hl : ∀ t ∈ S, 0 ≤ t + (U : ℤ)) :
    symbolOnPath (symbolEntry S p U r k) =
      frequencyExp (U : ℂ) * PowerSeries.derivative^[r] (trajectoryColumn S p k) := by
  rw [derivative_trajectoryColumn, Finset.mul_sum, symbolEntry, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  let φ := eval₂RingHom (PowerSeries.C : ℂ →+* PowerSeries ℂ) (PowerSeries.exp ℂ)
  have hφ : φ.comp (C : ℂ →+* ℂ[X]) = PowerSeries.C := eval₂RingHom_comp_C _ _
  have hz (q : ℂ[X]) : symbolOnPath (q.map (C : ℂ →+* ℂ[X])) = (q : PowerSeries ℂ) := by
    change (q.map (C : ℂ →+* ℂ[X])).eval₂ φ PowerSeries.X = _
    rw [eval₂_map, hφ, Polynomial.eval₂_C_X_eq_coe]
  have hy : symbolOnPath (C ((X : ℂ[X]) ^ shiftedFrequency U t)) =
      frequencyExp (U : ℂ) * frequencyExp (t : ℂ) := by
    change (C ((X : ℂ[X]) ^ shiftedFrequency U t)).eval₂ φ PowerSeries.X = _
    rw [eval₂_C, map_pow]
    rw [show φ (X : ℂ[X]) = PowerSeries.exp ℂ by
      simp only [φ, coe_eval₂RingHom, eval₂_X]]
    rw [PowerSeries.exp_pow_eq_rescale_exp, frequencyExp, frequencyExp,
      PowerSeries.exp_mul_exp_eq_exp_add]
    congr 2
    change ((t + U).toNat : ℂ) = (U : ℂ) + (t : ℂ)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hl t ht), Int.cast_add, Int.cast_natCast, add_comm]
  rw [map_mul, hy, hz, mul_assoc]

theorem symbolPolynomial_ne_zero {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X]) (U : ℕ)
    (hl : ∀ t ∈ S, 0 ≤ t + (U : ℤ)) (hd : ∀ t ∈ S, (p t).natDegree ≤ J)
    {t₀ : ℤ} (ht : t₀ ∈ S) (hp : p t₀ ≠ 0) (hdeg : (p t₀).natDegree = J) :
    symbolPolynomial S p U J ≠ 0 := by
  classical
  let f (k : Fin (J + 1)) := trajectoryColumn S p k.val
  have h := wronskian_det_ne_zero f (trajectory_columns_independent S p ht hp hdeg)
  have hM : symbolOnPath.mapMatrix (symbolMatrix S p U J) =
      Matrix.of (fun i j => frequencyExp (U : ℂ) * wronskianMatrix f i j) := by
    apply Matrix.ext
    intro i j
    exact symbolEntry_on_path S p U i.val j.val hl
  intro hz
  have he := symbolOnPath.map_det (symbolMatrix S p U J)
  rw [symbol_det_constant S p U J hd, hz, map_zero, map_zero, hM,
    Matrix.det_mul_column] at he
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun _ _ => frequencyExp_ne_zero _) h) he.symm

end PiPolynomialValues.FourPeriod
