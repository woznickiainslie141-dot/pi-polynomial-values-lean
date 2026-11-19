module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeMomentIdentity
public import OddPiPowers.Arithmetic.PrimeNumberRates
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The logarithmic prime measure gives the correct exact mass to every
affine cross-section in a fixed reciprocal window. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter Asymptotics OddPiPowers.PrimeRates
open scoped Topology

private theorem triangular_grows :
    Tendsto (fun n : ℕ => ∑ k ∈ range n, (k : ℝ)) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsub : Tendsto (fun n : ℕ => (n : ℝ)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hn
  simpa only [triangular_sum_real] using
    (hn.atTop_mul_atTop₀ hsub).atTop_div_const (by norm_num : (0 : ℝ) < 2)

private theorem triangular_rate :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, (k : ℝ)) / (n : ℝ)^2) atTop (𝓝 (1/2 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (1-1/(n : ℝ))/2) atTop (𝓝 ((1-0)/2 : ℝ)) :=
    (tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [triangular_sum_real]
  field_simp [Nat.cast_ne_zero.mpr hn.ne'] <;> ring

theorem primeMoment_ratio_tendsto :
    Tendsto (fun n : ℕ => primeMoment n / (n : ℝ)^2) atTop (𝓝 (1/2 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => Chebyshev.theta n / n) atTop (𝓝 1) :=
    theta_ratio_tendsto.comp tendsto_natCast_atTop_atTop
  have he : (fun n : ℕ => Chebyshev.theta n) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
    isEquivalent_of_tendsto_one ht
  have he' : (fun n : ℕ => ∑ k ∈ range n, Chebyshev.theta k) ~[atTop]
      (fun n : ℕ => ∑ k ∈ range n, (k : ℝ)) := by
    simpa only [IsEquivalent, Pi.sub_apply, Finset.sum_sub_distrib, Pi.sub_def] using
      he.isLittleO.sum_range (fun n => Nat.cast_nonneg n) triangular_grows
  have hpos := (triangular_grows.eventually (eventually_gt_atTop (0 : ℝ))).mono
    (fun n hn => hn.ne')
  have hq : Tendsto (fun n : ℕ =>
      (∑ k ∈ range n, Chebyshev.theta k) / (∑ k ∈ range n, (k : ℝ))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hpos).mp he'
  have h := ht.sub (hq.mul triangular_rate)
  norm_num only [one_mul, show (1 : ℝ) - 1/2 = 1/2 by norm_num] at h
  apply h.congr'
  filter_upwards [hpos, eventually_gt_atTop (0 : ℕ)] with n hs hn
  change Chebyshev.theta n / (n : ℝ) -
    ((∑ k ∈ range n, Chebyshev.theta k) / (∑ k ∈ range n, (k : ℝ))) *
      ((∑ k ∈ range n, (k : ℝ)) / (n : ℝ)^2) = primeMoment n / (n : ℝ)^2
  rw [primeMoment_identity]
  field_simp [Nat.cast_ne_zero.mpr hn.ne', hs] <;> ring

theorem primeMoment_scaled_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => primeMoment ⌊a * N⌋₊ / (N : ℝ)^2) atTop (𝓝 (a^2 / 2)) := by
  have hfloor := tendsto_nat_floor_mul_atTop a ha
  have hf : Tendsto (fun N : ℕ => (⌊a * N⌋₊ : ℝ) / N) atTop (𝓝 a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp tendsto_natCast_atTop_atTop
  have h := (primeMoment_ratio_tendsto.comp hfloor).mul (hf.pow 2)
  rw [show (1/2 : ℝ) * a^2 = a^2/2 by ring] at h
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_gt_atTop (0 : ℕ)),
    eventually_gt_atTop (0 : ℕ)] with n hk hn
  dsimp only [Function.comp_def]
  field_simp [Nat.cast_ne_zero.mpr hk.ne', Nat.cast_ne_zero.mpr hn.ne'] <;> ring

theorem window_primeMoment_tendsto (W : PrimeWindow) :
    Tendsto (fun N : ℕ => (∑ p ∈ W.primes N, (p : ℝ) * Real.log p) / (N : ℝ)^2)
      atTop (𝓝 ((W.lower⁻¹^2-W.upper⁻¹^2)/2)) := by
  have h := (primeMoment_scaled_tendsto (inv_pos.mpr W.lower_pos)).sub
    (primeMoment_scaled_tendsto (inv_pos.mpr W.upper_pos))
  simpa only [window_primeMoment, sub_div, div_eq_inv_mul (a := (_ : ℝ)) (b := W.lower),
    div_eq_inv_mul (a := (_ : ℝ)) (b := W.upper)] using h

end PiPolynomialValues.FourPeriod
