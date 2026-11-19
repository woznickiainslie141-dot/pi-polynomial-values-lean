module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeMomentRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter OddPiPowers.PrimeRates
open scoped Topology

/-- Fixed affine widths, including translating residue strips, can be used
directly in a logarithmically weighted prime sum. -/
theorem window_affine_tendsto (W : PrimeWindow) (a b : ℝ) :
    Tendsto (fun N : ℕ => (∑ p ∈ W.primes N, (a+b*((p : ℝ)/N))*Real.log p) / N) atTop
      (𝓝 ((W.lower⁻¹-W.upper⁻¹) * (a+b*(W.upper⁻¹+W.lower⁻¹)/2))) := by
  have hsum (N : ℕ) :
      a*((∑ p ∈ W.primes N, Real.log p) / N) +
        b*((∑ p ∈ W.primes N, (p : ℝ)*Real.log p) / (N : ℝ)^2) =
      (∑ p ∈ W.primes N, (a+b*((p : ℝ)/N))*Real.log p) / N := by
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hn : (N : ℝ) = 0
    · simp [hn]
    · field_simp [hn] <;> ring
  have h := ((W.log_sum_div_tendsto.const_mul a).add ((window_primeMoment_tendsto W).const_mul b)).congr hsum
  have he : a*(1/W.lower-1/W.upper) + b*((W.lower⁻¹^2-W.upper⁻¹^2)/2) =
      (W.lower⁻¹-W.upper⁻¹)*(a+b*(W.upper⁻¹+W.lower⁻¹)/2) := by
    simp only [one_div]
    ring
  rwa [he] at h

end PiPolynomialValues.FourPeriod
