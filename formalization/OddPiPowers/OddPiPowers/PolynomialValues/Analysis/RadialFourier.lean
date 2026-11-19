module

public import OddPiPowers.PolynomialValues.Analysis.RadialKernel
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! A radial logarithmic interaction has nonpositive quadratic energy
for arbitrary finite signed weights, including atomic ones. -/

@[expose] public section

namespace PiPolynomialValues

open scoped ComplexConjugate
open Finset

noncomputable def radialFourierWeight (r : ℝ) (k : ℕ) := r^(k+1)/(k+1 : ℕ)

theorem log_radial_chord_hasSum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {u : ℂ} (hu : ‖u‖ = 1) :
    HasSum (fun k : ℕ => radialFourierWeight r k*(u^(k+1)).re)
      (-Real.log ‖1-(r : ℂ)*u‖) := by
  have hz : ‖(r : ℂ)*u‖ < 1 := by
    simpa [norm_mul,hu,abs_of_nonneg hr] using hr1
  have H := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hz)
  simp only [Complex.neg_re,Complex.log_re] at H
  refine H.congr_fun fun k => ?_
  have h : ((r : ℂ)*u)^(k+1)/(k+1 : ℂ) = (radialFourierWeight r k : ℂ)*u^(k+1) := by
    unfold radialFourierWeight
    push_cast
    rw [mul_pow]
    ring
  rw [h,Complex.re_ofReal_mul]

theorem radialPair_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : 0 < radialPair r u v := by
  have h (w : ℂ) (hw : ‖w‖ = 1) : 0 < ‖1-(r : ℂ)*w‖ := by
    have hh : 1-r ≤ ‖1-(r : ℂ)*w‖ := by
      simpa [norm_mul,hw,abs_of_nonneg hr] using (norm_sub_norm_le (1 : ℂ) ((r : ℂ)*w))
    linarith
  exact mul_pos (h _ (by simp [norm_mul,hu,hv])) (h _ (by simp [norm_mul,hu,hv]))

theorem log_radial_pair_hasSum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    HasSum (fun k : ℕ => -2*radialFourierWeight r k*(u^(k+1)).re*(v^(k+1)).re)
      (Real.log (radialPair r u v)) := by
  have ha := log_radial_chord_hasSum hr hr1 (u := u*v) (by simp [norm_mul,hu,hv])
  have hb := log_radial_chord_hasSum hr hr1 (u := u*conj v) (by simp [norm_mul,hu,hv])
  have hp := radialPair_pos hr hr1 hu hv
  have hh := (ha.add hb).neg
  unfold radialPair at hp ⊢
  rw [Real.log_mul (left_ne_zero_of_mul hp.ne') (right_ne_zero_of_mul hp.ne')]
  simp only [neg_add_rev,neg_neg] at hh
  rw [add_comm]
  refine hh.congr_fun fun k => ?_
  simp only [mul_pow,← map_pow,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

noncomputable def atomicRadialEnergy {ι : Type*} [Fintype ι] (r : ℝ) (w : ι → ℝ)
    (u : ι → ℂ) : ℝ := ∑ i, ∑ j, w i*w j*Real.log (radialPair r (u i) (u j))

theorem atomicRadialEnergy_nonpos {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) (w : ι → ℝ) (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    atomicRadialEnergy r w u ≤ 0 := by
  classical
  let b (k : ℕ) (i : ι) := (u i^(k+1)).re
  have h (i j : ι) := (log_radial_pair_hasSum hr hr1 (hu i) (hu j)).mul_left (w i*w j)
  have s := hasSum_sum fun i (_ : i ∈ (univ : Finset ι)) =>
    hasSum_sum fun j (_ : j ∈ (univ : Finset ι)) => h i j
  change (∑ i, ∑ j, _) ≤ 0
  apply le_of_tendsto s
  filter_upwards with F
  apply sum_nonpos
  intro k _
  have he : (∑ i, ∑ j, w i*w j*(-2*radialFourierWeight r k*b k i*b k j)) =
      -2*radialFourierWeight r k*(∑ i, w i*b k i)^2 := by
    calc
      _ = ∑ i, (-2*radialFourierWeight r k*(w i*b k i))*(∑ j, w j*b k j) := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [← sum_mul,← mul_sum]; ring
  change (∑ i, ∑ j, w i*w j*(-2*radialFourierWeight r k*b k i*b k j)) ≤ 0
  rw [he]
  have hw : 0 ≤ radialFourierWeight r k := by unfold radialFourierWeight; positivity
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hw) (sq_nonneg _)

end PiPolynomialValues
