module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxLattice
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeAffineRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The real area of a trapezoid is attained as a lower rate for the actual
logarithmically weighted integer residue counts. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Filter MeasureTheory Finset
open scoped Topology Interval

private theorem residue_sum_lower (W : OddPiPowers.PrimeRates.PrimeWindow) (b : Box) (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ W.primes N, stripWidth b ((p : ℝ)/N)*Real.log p)/N -
      ((∑ p ∈ W.primes N, Real.log p)/N)/N ≤
      (∑ p ∈ W.primes N, ((residuePoints b N p).card : ℝ)*Real.log p)/(N : ℝ)^2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [sum_div, ← sum_sub_distrib]
  apply sum_le_sum
  intro p hp
  have hprime := ((W.mem_primes N p).mp hp).1
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
  have h := mul_le_mul_of_nonneg_right (residuePoints_card_lower b N p hN hprime.pos)
    (Real.log_nonneg hp')
  calc
    _ = (((N : ℝ)*stripWidth b ((p : ℝ)/N)-1)*Real.log p)/(N : ℝ)^2 := by
      field_simp [hN'.ne'] <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right h (sq_nonneg _)

theorem residue_prime_sum_eventually (W : OddPiPowers.PrimeRates.PrimeWindow) (b : Box) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ y in W.upper⁻¹..W.lower⁻¹, stripWidth b y) - ε ≤
      (∑ p ∈ W.primes N, ((residuePoints b N p).card : ℝ)*Real.log p)/(N : ℝ)^2 := by
  let I : ℝ := ∫ y in W.upper⁻¹..W.lower⁻¹, stripWidth b y
  have ha : Tendsto (fun N : ℕ =>
      (∑ p ∈ W.primes N, stripWidth b ((p : ℝ)/N)*Real.log p)/N) atTop (𝓝 I) := by
    simp only [I, stripWidth, integral_affine_real]
    exact window_affine_tendsto W _ _
  have hz : Tendsto (fun N : ℕ => ((∑ p ∈ W.primes N, Real.log p)/N)/N) atTop (𝓝 0) := by
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero] using W.log_sum_div_tendsto.mul hi
  have hh := ha.sub hz
  rw [sub_zero] at hh
  have he := hh.eventually (lt_mem_nhds (show I-ε < I by linarith))
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N h hN
  exact h.le.trans (residue_sum_lower W b N hN)

end PiPolynomialValues.PrimeWindow
