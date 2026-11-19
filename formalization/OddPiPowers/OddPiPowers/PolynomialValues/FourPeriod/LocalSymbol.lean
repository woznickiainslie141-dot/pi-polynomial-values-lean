module

public import OddPiPowers.PolynomialValues.FourPeriod.SymbolOnPath
public import OddPiPowers.PolynomialValues.FourPeriod.Translation
public import OddPiPowers.PolynomialValues.FourPeriod.ContactOrder

/-! Evaluate the same two-variable determinant on the path through each
nonzero base point. Its frequency shift is a unit in the power series ring. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

noncomputable def localSymbolPath (ρ : ℂ) : Polynomial (ℂ[X]) →+* PowerSeries ℂ :=
  eval₂RingHom (exponentialPath ρ) PowerSeries.X

theorem derivative_localColumn (ρ : ℂ) (S : Finset ℤ) (p : ℤ → ℂ[X]) (r k : ℕ) :
    PowerSeries.derivative^[r] (localColumn ρ S p k) =
      ∑ t ∈ S, ρ ^ t • (frequencyExp (t : ℂ) *
        ((rowOperator 1 (t : ℂ) r (Polynomial.derivative^[k] (p t)) : ℂ[X]) : PowerSeries ℂ)) := by
  let D : Module.End ℂ (PowerSeries ℂ) := PowerSeries.derivative.toLinearMap
  change D^[r] (∑ t ∈ S, _) = _
  rw [← Module.End.pow_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [(D^r).map_smul, Module.End.pow_apply]
  exact congrArg (fun f : PowerSeries ℂ => ρ ^ t • f)
    (derivative_frequency_mul_row (t : ℂ) (Polynomial.derivative^[k] (p t)) r)

private theorem exponential_shift {ρ : ℂ} (hρ : ρ ≠ 0) (U : ℕ) (t : ℤ)
    (ht : 0 ≤ t+(U : ℤ)) :
    (PowerSeries.C ρ * PowerSeries.exp ℂ) ^ shiftedFrequency U t =
      (PowerSeries.C ρ * PowerSeries.exp ℂ) ^ U *
        (PowerSeries.C (ρ^t) * frequencyExp (t : ℂ)) := by
  have hpow : ρ ^ shiftedFrequency U t = ρ ^ U * ρ ^ t := by
    rw [← zpow_natCast, shiftedFrequency, Int.toNat_of_nonneg ht, zpow_add₀ hρ, zpow_natCast,
      mul_comm]
  have he : PowerSeries.exp ℂ ^ shiftedFrequency U t =
      PowerSeries.exp ℂ ^ U * frequencyExp (t : ℂ) := by
    rw [PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.exp_pow_eq_rescale_exp, frequencyExp,
      PowerSeries.exp_mul_exp_eq_exp_add]
    congr 2
    change ((t+U).toNat : ℂ) = (U : ℂ)+(t : ℂ)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg ht, Int.cast_add, Int.cast_natCast, add_comm]
  rw [mul_pow, mul_pow, ← map_pow, hpow, map_mul, map_pow, he]
  ring

theorem symbolEntry_on_localPath {ρ : ℂ} (hρ : ρ ≠ 0) (S : Finset ℤ) (p : ℤ → ℂ[X])
    (U r k : ℕ) (hl : ∀ t ∈ S, 0 ≤ t+(U : ℤ)) :
    localSymbolPath ρ (symbolEntry S p U r k) =
      (PowerSeries.C ρ * PowerSeries.exp ℂ)^U *
        PowerSeries.derivative^[r] (localColumn ρ S p k) := by
  have hφ : (exponentialPath ρ).comp (C : ℂ →+* ℂ[X]) = PowerSeries.C :=
    eval₂RingHom_comp_C _ _
  have hz (q : ℂ[X]) : localSymbolPath ρ (q.map (C : ℂ →+* ℂ[X])) = (q : PowerSeries ℂ) := by
    change (q.map (C : ℂ →+* ℂ[X])).eval₂ (exponentialPath ρ) PowerSeries.X = _
    rw [eval₂_map, hφ, Polynomial.eval₂_C_X_eq_coe]
  rw [derivative_localColumn, Finset.mul_sum, symbolEntry, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hy : localSymbolPath ρ (C ((X : ℂ[X]) ^ shiftedFrequency U t)) =
      (PowerSeries.C ρ * PowerSeries.exp ℂ)^U *
        (PowerSeries.C (ρ^t) * frequencyExp (t : ℂ)) := by
    calc
      _ = (PowerSeries.C ρ * PowerSeries.exp ℂ)^shiftedFrequency U t := by
        simp only [localSymbolPath, exponentialPath, coe_eval₂RingHom, eval₂_C, eval₂_pow, eval₂_X]
      _ = _ := exponential_shift hρ U t (hl t ht)
  rw [map_mul, hy, hz, PowerSeries.smul_eq_C_mul]
  ring

theorem order_symbol_localPath {ρ : ℂ} (hρ : ρ ≠ 0) (S : Finset ℤ) (p : ℤ → ℂ[X])
    (U J : ℕ) (hl : ∀ t ∈ S, 0 ≤ t+(U : ℤ)) (hd : ∀ t ∈ S, (p t).natDegree ≤ J) :
    (exponentialPath ρ (symbolPolynomial S p U J)).order =
      (wronskianMatrix (fun k : Fin (J+1) => localColumn ρ S p k.val)).det.order := by
  let M := wronskianMatrix (fun k : Fin (J+1) => localColumn ρ S p k.val)
  let v : PowerSeries ℂ := (PowerSeries.C ρ * PowerSeries.exp ℂ)^U
  have hv : IsUnit v :=
    (((isUnit_iff_ne_zero.mpr hρ).map (PowerSeries.C : ℂ →+* PowerSeries ℂ)).mul
      (PowerSeries.isUnit_exp ℂ)).pow U
  have hm : (localSymbolPath ρ).mapMatrix (symbolMatrix S p U J) =
      Matrix.of (fun i j => v * M i j) := by
    apply Matrix.ext
    intro i j
    exact symbolEntry_on_localPath hρ S p U i.val j.val hl
  have he : exponentialPath ρ (symbolPolynomial S p U J) = v^(J+1)*M.det := by
    calc
      _ = localSymbolPath ρ (symbolMatrix S p U J).det := by
        rw [symbol_det_constant S p U J hd]
        simp [localSymbolPath]
      _ = _ := by
        rw [RingHom.map_det, hm, Matrix.det_mul_column]
        simp
  rw [he, PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit (hv.pow _), zero_add]

end PiPolynomialValues.FourPeriod
