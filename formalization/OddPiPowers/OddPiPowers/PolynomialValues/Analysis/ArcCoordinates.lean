module

public import OddPiPowers.PolynomialValues.Analysis.FoldedSine
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Parameterize a closed angular cell by its rational half-angle endpoints. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory

def halfAngleSin {K : Type*} [Field K] (t : K) := 2*t/(1+t^2)
def halfAngleCos {K : Type*} [Field K] (t : K) := (1-t^2)/(1+t^2)

def arcMassArg {K : Type*} [Field K] (z l r : K) : K :=
  let g := (1+z^2)/(1-z^2)
  ((g*halfAngleCos l)*halfAngleSin r-(g*halfAngleSin l)*halfAngleCos r)/
    (halfAngleCos l*halfAngleCos r+(g^2*halfAngleSin l)*halfAngleSin r)

def arcSineArg {K : Type*} [Field K] (z l r : K) : K :=
  let k := 2*z/(1+z^2)
  (k*halfAngleCos l-k*halfAngleCos r)/(1-(k*halfAngleCos l)*(k*halfAngleCos r))

theorem sin_two_arctan (t : ℝ) : sin (2*arctan t) = halfAngleSin t := by
  have h : 0 < 1+t^2 := by positivity
  have hroot := Real.sqrt_pos.mpr h
  rw [sin_two_mul, sin_arctan, cos_arctan]
  calc
    _ = 2*t / (Real.sqrt (1+t^2))^2 := by field_simp [hroot.ne'] <;> ring
    _ = _ := by rw [Real.sq_sqrt h.le] <;> rfl

theorem cos_two_arctan (t : ℝ) : cos (2*arctan t) = halfAngleCos t := by
  have h : 0 < 1+t^2 := by positivity
  have hroot := Real.sqrt_pos.mpr h
  rw [cos_two_mul, cos_arctan]
  calc
    _ = 2 / (Real.sqrt (1+t^2))^2 - 1 := by field_simp [hroot.ne'] <;> ring
    _ = _ := by
      rw [Real.sq_sqrt h.le]
      unfold halfAngleCos
      field_simp [h.ne'] <;> ring

private theorem foldDot_quadrant {g a b : ℝ} (hg : 0 < g) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ π/2) (hs : 0 < a ∨ b < π/2)
    {t : ℝ} (ht : t ∈ Set.uIcc a b) : 0 < foldDot g a t := by
  rw [Set.uIcc_of_le hab] at ht
  have hc (v : ℝ) (hv : a ≤ v) (hw : v ≤ b) : 0 ≤ cos v :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hw.trans hb⟩
  have hn (v : ℝ) (hv : a ≤ v) (hw : v ≤ b) : 0 ≤ sin v :=
    sin_nonneg_of_nonneg_of_le_pi (ha.trans hv) (by linarith [pi_pos])
  unfold foldDot
  rcases hs with h | h
  · have hs' (v : ℝ) (hv : a ≤ v) (hw : v ≤ b) : 0 < sin v :=
      sin_pos_of_pos_of_lt_pi (h.trans_le hv) (by linarith [pi_pos])
    exact add_pos_of_nonneg_of_pos (mul_nonneg (hc a le_rfl hab) (hc t ht.1 ht.2))
      (mul_pos (mul_pos (sq_pos_of_pos hg) (hs' a le_rfl hab)) (hs' t ht.1 ht.2))
  · have hc' (v : ℝ) (hv : a ≤ v) (hw : v ≤ b) : 0 < cos v :=
      cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hw.trans_lt h⟩
    exact add_pos_of_pos_of_nonneg (mul_pos (hc' a le_rfl hab) (hc' t ht.1 ht.2))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (hn a le_rfl hab)) (hn t ht.1 ht.2))

theorem foldedPoisson_halfAngle_integrals {z l r : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hshort : 0 < l ∨ r < 1) :
    (∫ t in (2*arctan l)..(2*arctan r), foldedPoisson z t) = (2/π)*arctan (arcMassArg z l r) ∧
    (∫ t in (2*arctan l)..(2*arctan r), foldedPoisson z t * sin t) =
      (1-z^2)/(π*z)*halfLogRatio (arcSineArg z l r) := by
  have ha : 0 ≤ 2*arctan l := by linarith [arctan_nonneg.mpr hl]
  have hab : 2*arctan l ≤ 2*arctan r := by linarith [arctan_strictMono.monotone hlr]
  have hb : 2*arctan r ≤ π/2 := by
    have hh := arctan_strictMono.monotone hr
    rw [arctan_one] at hh
    linarith
  have hs : 0 < 2*arctan l ∨ 2*arctan r < π/2 := by
    rcases hshort with h | h
    · left
      have hh := arctan_strictMono h
      rw [arctan_zero] at hh
      linarith
    · right
      have hh := arctan_strictMono h
      rw [arctan_one] at hh
      linarith
  constructor
  · rw [integral_foldedPoisson_arc hz hz1 _ _ (fun _ ht =>
      (foldDot_quadrant (foldStretch_pos hz hz1) ha hab hb hs ht).ne')]
    simp only [foldDot, foldCross, foldStretch, sin_two_arctan, cos_two_arctan, arcMassArg]
  · rw [integral_foldedPoisson_sine_arc hz hz1]
    simp only [foldCosScale, cos_two_arctan, arcSineArg]

end PiPolynomialValues
