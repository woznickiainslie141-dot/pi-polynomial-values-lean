module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Analysis.Complex.Basic

/-! Polynomial exponentials with distinct integer frequencies cannot cancel as
formal power series. Differentiation separates their generalized eigenspaces. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial
open scoped PowerSeries

noncomputable def frequencyExp (t : ℂ) : PowerSeries ℂ := PowerSeries.rescale t (PowerSeries.exp ℂ)

theorem frequencyExp_ne_zero (t : ℂ) : frequencyExp t ≠ 0 := by
  intro h
  have he := congrArg (PowerSeries.coeff 0) h
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [frequencyExp, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_exp, map_zero] using he

theorem derivative_frequencyExp (t : ℂ) :
    PowerSeries.derivative (frequencyExp t) = PowerSeries.C t * frequencyExp t := by
  ext n
  have h := congrArg (PowerSeries.coeff n) (PowerSeries.derivative_exp ℂ)
  rw [PowerSeries.coeff_derivative] at h
  simp only [frequencyExp, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, pow_succ]
  calc
    _ = t * t ^ n * (PowerSeries.coeff (n + 1) (PowerSeries.exp ℂ) * (n + 1)) := by ring
    _ = _ := by rw [h]; ring

private noncomputable abbrev D : Module.End ℂ (PowerSeries ℂ) := PowerSeries.derivative.toLinearMap

private theorem shift_derivative_frequency (t : ℂ) (p : ℂ[X]) :
    (D - t • 1) (frequencyExp t * (p : PowerSeries ℂ)) =
      frequencyExp t * (p.derivative : PowerSeries ℂ) := by
  change PowerSeries.derivative (frequencyExp t * (p : PowerSeries ℂ)) -
      t • (frequencyExp t * (p : PowerSeries ℂ)) = _
  rw [PowerSeries.derivative.leibniz, PowerSeries.derivative_coe, derivative_frequencyExp,
    PowerSeries.smul_eq_C_mul]
  simp only [smul_eq_mul]
  ring

theorem frequencyExp_mul_mem_genEigenspace (t : ℂ) (p : ℂ[X]) :
    frequencyExp t * (p : PowerSeries ℂ) ∈
      Module.End.genEigenspace (PowerSeries.derivative.toLinearMap : Module.End ℂ (PowerSeries ℂ)) t ⊤ := by
  have hpow (k : ℕ) : ((D - t • 1) ^ k) (frequencyExp t * (p : PowerSeries ℂ)) =
      frequencyExp t * ((Polynomial.derivative^[k] p : ℂ[X]) : PowerSeries ℂ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, shift_derivative_frequency, Function.iterate_succ_apply']
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨p.natDegree + 1, LinearMap.mem_ker.mpr ?_⟩
  rw [hpow, Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _), Polynomial.coe_zero, mul_zero]

/-- Injectivity on finite exponential polynomials with polynomial coefficients
of arbitrary degree. In particular, each Laurent frequency in the row-selection
argument is retained under the substitution y = exp(w), z = w. -/
theorem exp_polynomial_sum_eq_zero_iff (S : Finset ℤ) (p : ℤ → ℂ[X]) :
    (∑ t ∈ S, frequencyExp (t : ℂ) * (p t : PowerSeries ℂ)) = 0 ↔ ∀ t ∈ S, p t = 0 := by
  constructor
  · intro hs
    have hind := (D.independent_genEigenspace ⊤).comp (Int.cast_injective (α := ℂ))
    have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind S
      (fun t : ℤ => frequencyExp (t : ℂ) * (p t : PowerSeries ℂ))
      (fun t _ => frequencyExp_mul_mem_genEigenspace _ _) hs
    intro t ht
    exact Polynomial.coe_eq_zero_iff.mp ((mul_eq_zero.mp (h t ht)).resolve_left (frequencyExp_ne_zero _))
  · intro hp
    exact Finset.sum_eq_zero fun t ht => by simp [hp t ht]

end PiPolynomialValues.FourPeriod
