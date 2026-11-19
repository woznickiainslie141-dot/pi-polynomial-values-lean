module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBox
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Endpoint integer divisions control a floor at every interior point of
a trapezoid. The strict upper quotient also covers an integral endpoint. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

noncomputable def Abscissa.value (t : Abscissa) : ℝ := (t.num : ℝ) / t.den

noncomputable def Boundary.value (f : Boundary) (t : ℝ) : ℝ :=
  (f.slope : ℝ) / 10000 * t + (f.offset : ℝ) / 2

theorem affine_numerator (f : Boundary) (l : Abscissa) (hl : 0 < l.den) :
    f.value l.value = (f.ordinate l : ℝ) / (20000 * (l.den : ℝ)) := by
  have h : (l.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  unfold Boundary.value Abscissa.value Boundary.ordinate
  push_cast
  field_simp [h]
  ring

theorem integer_lower_floor (n d : ℤ) (hd : 0 < d) {x : ℝ} (hx : (n : ℝ) / d ≤ x) :
    n / d ≤ ⌊x⌋ := by
  apply Int.le_floor.mpr
  apply le_trans _ hx
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast Int.ediv_mul_le n hd.ne'

theorem integer_upper_floor (n d : ℤ) (hd : 0 < d) {x : ℝ} (hx : x < (n : ℝ) / d) :
    ⌊x⌋ ≤ (n - 1) / d := by
  apply (Int.le_ediv_iff_mul_le hd).mpr
  have h := (lt_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp ((Int.floor_le x).trans_lt hx)
  have h' : ⌊x⌋ * d < n := by exact_mod_cast h
  omega

private theorem lower_at_end (f : Boundary) (l : Abscissa) (hl : 0 < l.den)
    {x : ℝ} (hx : f.value l.value ≤ x) : f.lowerFloor l ≤ ⌊x⌋ := by
  have hd : (0 : ℤ) < l.den := by exact_mod_cast hl
  apply integer_lower_floor _ _ (mul_pos (by decide : (0 : ℤ) < 20000) hd)
  simpa only [affine_numerator f l hl, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hx

private theorem upper_at_end (f : Boundary) (l : Abscissa) (hl : 0 < l.den)
    {x : ℝ} (hx : x < f.value l.value) : ⌊x⌋ ≤ f.strictUpperFloor l := by
  have hd : (0 : ℤ) < l.den := by exact_mod_cast hl
  apply integer_upper_floor _ _ (mul_pos (by decide : (0 : ℤ) < 20000) hd)
  simpa only [affine_numerator f l hl, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hx

theorem Boundary.monotone_or_antitone (f : Boundary) : Monotone f.value ∨ Antitone f.value := by
  rcases le_total (0 : ℝ) (f.slope / 10000 : ℝ) with h | h
  · exact Or.inl (fun _ _ ht => add_le_add (mul_le_mul_of_nonneg_left ht h) le_rfl)
  · exact Or.inr (fun _ _ ht => add_le_add (mul_le_mul_of_nonpos_left ht h) le_rfl)

theorem affine_lower_floor (f : Boundary) (l r : Abscissa) (hl : 0 < l.den) (hr : 0 < r.den)
    {t x : ℝ} (hlt : l.value ≤ t) (htr : t ≤ r.value) (hx : f.value t ≤ x) :
    min (f.lowerFloor l) (f.lowerFloor r) ≤ ⌊x⌋ := by
  rcases f.monotone_or_antitone with hm | ha
  · exact (min_le_left _ _).trans (lower_at_end f l hl ((hm hlt).trans hx))
  · exact (min_le_right _ _).trans (lower_at_end f r hr ((ha htr).trans hx))

theorem affine_upper_floor (f : Boundary) (l r : Abscissa) (hl : 0 < l.den) (hr : 0 < r.den)
    {t x : ℝ} (hlt : l.value ≤ t) (htr : t ≤ r.value) (hx : x < f.value t) :
    ⌊x⌋ ≤ max (f.strictUpperFloor l) (f.strictUpperFloor r) := by
  rcases f.monotone_or_antitone with hm | ha
  · exact (upper_at_end f r hr (hx.trans_le (hm htr))).trans (le_max_right _ _)
  · exact (upper_at_end f l hl (hx.trans_le (ha hlt))).trans (le_max_left _ _)

theorem widthMinus_value (w : ℕ) (f : Boundary) (t : ℝ) :
    (widthMinus w f).value t = (w : ℝ) / 10000 * t - f.value t := by
  simp only [Boundary.value, widthMinus, Int.cast_sub, Int.cast_natCast, Int.cast_neg]
  ring

theorem widthPlus_value (w : ℕ) (f : Boundary) (t : ℝ) :
    (widthPlus w f).value t = (w : ℝ) / 10000 * t + f.value t := by
  simp only [Boundary.value, widthPlus, Int.cast_add, Int.cast_natCast]
  ring

noncomputable def bandCount (w : ℕ) (t τ : ℝ) : ℤ :=
  1 + ⌊(w : ℝ) / 10000 * t - τ⌋ + ⌊(w : ℝ) / 10000 * t + τ⌋

theorem band_count_between (l r : Abscissa) (b : Box) (w : ℕ) (hl : 0 < l.den) (hr : 0 < r.den)
    {t τ : ℝ} (hlt : l.value ≤ t) (htr : t ≤ r.value) (hbot : b.bottom.value t < τ)
    (htop : τ < b.top.value t) :
    lowBand l r b w ≤ bandCount w t τ ∧ bandCount w t τ ≤ highBand l r b w := by
  have lm := affine_lower_floor (widthMinus w b.top) l r hl hr hlt htr
    (x := (w : ℝ) / 10000 * t - τ) (by rw [widthMinus_value]; linarith)
  have lp := affine_lower_floor (widthPlus w b.bottom) l r hl hr hlt htr
    (x := (w : ℝ) / 10000 * t + τ) (by rw [widthPlus_value]; linarith)
  have um := affine_upper_floor (widthMinus w b.bottom) l r hl hr hlt htr
    (x := (w : ℝ) / 10000 * t - τ) (by rw [widthMinus_value]; linarith)
  have up := affine_upper_floor (widthPlus w b.top) l r hl hr hlt htr
    (x := (w : ℝ) / 10000 * t + τ) (by rw [widthPlus_value]; linarith)
  exact ⟨add_le_add (add_le_add le_rfl lm) lp, add_le_add (add_le_add le_rfl um) up⟩

end PiPolynomialValues.PrimeWindow
