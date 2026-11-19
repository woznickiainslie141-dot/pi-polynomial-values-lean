module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A uniform upper bound for the logarithmic interaction of the discrete
frequencies, valid also for repeated frequencies. The radial kernel has a
finite value on the diagonal. -/

@[expose] public section

namespace PiPolynomialValues

open scoped ComplexConjugate

private theorem unit_mul_conj {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, ← Complex.sq_norm, hz]
  norm_num

theorem two_abs_real_sub_of_unit {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    2 * |u.re - v.re| = ‖1 - u * v‖ * ‖1 - u * conj v‖ := by
  have he : (1 - u * v) * (1 - u * conj v) = u * ((u + conj u) - (v + conj v)) := by
    calc
      _ = 1 - u * (v + conj v) + u ^ 2 * (v * conj v) := by ring
      _ = _ := by
        rw [unit_mul_conj hv, mul_one]
        linear_combination -(unit_mul_conj hu)
  rw [← norm_mul, he, norm_mul, hu, one_mul, Complex.add_conj, Complex.add_conj,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub, abs_mul]
  norm_num

theorem radial_chord_square {z : ℂ} (hz : ‖z‖ = 1) (r : ℝ) :
    ‖1 - (r : ℂ) * z‖ ^ 2 = (1 - r) ^ 2 + r * ‖1 - z‖ ^ 2 := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  calc
    _ = 1 - 2 * r * z.re + r ^ 2 * (z.re * z.re + z.im * z.im) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_im,
        Complex.one_im, Complex.mul_im, add_zero]
      ring
    _ = (1 - r) ^ 2 + r * (1 - 2 * z.re + (z.re * z.re + z.im * z.im)) := by rw [h]; ring
    _ = _ := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
        Complex.sub_im, Complex.one_im]
      ring

private theorem radial_chord_lower {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt r * ‖1 - z‖ ≤ ‖1 - (r : ℂ) * z‖ := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hr, radial_chord_square hz]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem radial_chord_gap {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    1 - r ≤ ‖1 - (r : ℂ) * z‖ := by
  simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    hz, mul_one] using (norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z))

noncomputable def radialPair (r : ℝ) (u v : ℂ) : ℝ :=
  ‖1 - (r : ℂ) * (u * v)‖ * ‖1 - (r : ℂ) * (u * conj v)‖

theorem regularized_pair_bound {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 ≤ ε) :
    2 * (|u.re - v.re| + ε) ≤ (1 / r + 2 * ε / (1 - r) ^ 2) * radialPair r u v := by
  have ha : ‖u * v‖ = 1 := by rw [norm_mul, hu, hv, mul_one]
  have hb : ‖u * conj v‖ = 1 := by rw [norm_mul, Complex.norm_conj, hu, hv, mul_one]
  have hm : r * (2 * |u.re - v.re|) ≤ radialPair r u v := by
    calc
      _ = Real.sqrt r ^ 2 * (‖1 - u * v‖ * ‖1 - u * conj v‖) := by
        rw [Real.sq_sqrt hr.le, two_abs_real_sub_of_unit hu hv]
      _ = (Real.sqrt r * ‖1 - u * v‖) * (Real.sqrt r * ‖1 - u * conj v‖) := by ring
      _ ≤ _ := mul_le_mul (radial_chord_lower ha hr.le) (radial_chord_lower hb hr.le)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hgap : (1 - r) ^ 2 ≤ radialPair r u v := by
    rw [sq]
    exact mul_le_mul (radial_chord_gap ha hr.le) (radial_chord_gap hb hr.le)
      (sub_nonneg.mpr hr1.le) (norm_nonneg _)
  have hpos : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  have h₁ : 2 * |u.re - v.re| ≤ radialPair r u v / r :=
    (le_div_iff₀ hr).mpr (by simpa only [mul_comm r] using hm)
  have h₂ : 2 * ε ≤ (2 * ε / (1 - r) ^ 2) * radialPair r u v := by
    calc
      _ = (2 * ε / (1 - r) ^ 2) * (1 - r) ^ 2 := (div_mul_cancel₀ _ hpos.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (div_nonneg (by linarith) hpos.le)
  calc
    _ = 2 * |u.re - v.re| + 2 * ε := by ring
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

end PiPolynomialValues
