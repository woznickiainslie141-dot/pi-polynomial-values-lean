module

public import OddPiPowers.Arithmetic.PrimeWindowSums
import Mathlib.Tactic.Ring

/-! The first moment of the logarithmic prime measure, by finite summation
by parts. The reciprocal windows are those of the accepted theta theorem. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset OddPiPowers.PrimeRates

noncomputable def primeMoment (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, (p : ℝ) * Real.log p

theorem primeMoment_identity (n : ℕ) :
    primeMoment n = (n : ℝ) * Chebyshev.theta n -
      ∑ k ∈ range n, Chebyshev.theta k := by
  simp only [primeMoment, Chebyshev.theta_eq_sum_primesLE_log]
  induction n with
  | zero => simp [Nat.primesLE_zero]
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.primesLE_succ n]
    by_cases hp : (n+1).Prime
    · simp only [if_pos hp, Finset.sum_insert (Nat.notMem_primesLE n), ih, Nat.cast_succ]
      ring
    · simp only [if_neg hp, ih, Nat.cast_succ]
      ring

theorem window_primeMoment (W : PrimeWindow) (N : ℕ) :
    (∑ p ∈ W.primes N, (p : ℝ) * Real.log p) =
      primeMoment ⌊(N : ℝ) / W.lower⌋₊ - primeMoment ⌊(N : ℝ) / W.upper⌋₊ := by
  apply Finset.sum_sdiff_eq_sub
  exact Nat.primesLE_mono (Nat.floor_le_floor
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) W.lower_pos W.lower_lt_upper.le))

theorem triangular_sum_real (n : ℕ) :
    (∑ k ∈ range n, (k : ℝ)) = (n : ℝ) * ((n : ℝ)-1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

end PiPolynomialValues.FourPeriod
