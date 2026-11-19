module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

public section

namespace PiPolynomialValues

open scoped BigOperators

/-- A supporting level certifies a global minimum on the entire simplex.
    The labels, their number, and the subset carrying positive mass are arbitrary. -/
theorem simplex_minimum_of_contact {ι : Type*} [Fintype ι]
    (a q p : ι → ℝ) (B θ : ℝ)
    (hB : 0 ≤ B) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hlevel : ∀ i, θ ≤ a i + 2 * B * q i)
    (hcontact : ∀ i, (a i + 2 * B * q i - θ) * q i = 0) :
    ∑ i, (a i * q i + B * (q i) ^ 2) ≤ ∑ i, (a i * p i + B * (p i) ^ 2) := by
  have term (i : ι) :
      (a i * q i + B * (q i) ^ 2) + θ * (p i - q i) ≤
      a i * p i + B * (p i) ^ 2 := by
    have hlin := mul_nonneg (sub_nonneg.mpr (hlevel i)) (hp i)
    have hsquare := mul_nonneg hB (sq_nonneg (p i - q i))
    nlinarith only [hlin, hsquare, hcontact i]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => term i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hpsum, hqsum, sub_self, mul_zero, add_zero] using hsum

/-- Strict saving at the principal root and a nonnegative secondary saving
    contradict nonnegativity of the normalized logarithm of a nonzero integer. -/
theorem impossible_resultant_rate {rate A F m γ y : ℝ}
    (arith : 0 ≤ rate) (estimate : rate ≤ A - F + (m - γ) * y)
    (main : A < F) (secondary : m ≤ γ) (hy : 0 ≤ y) : False := by
  have hcorrection := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr secondary) hy
  linarith

end PiPolynomialValues
