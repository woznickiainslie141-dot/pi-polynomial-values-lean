module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxFloor
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeLevels
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-! Integer lifts in each band and pointwise collision cost in an entire
open trapezoid. The two signs of the supporting slope use opposite bounds. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

noncomputable def lifts (w : ℕ) (t τ : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊(w : ℝ) / 10000 * t + τ⌋) ⌊(w : ℝ) / 10000 * t - τ⌋

theorem mem_lifts (w : ℕ) (t τ : ℝ) (j : ℤ) :
    j ∈ lifts w t τ ↔ |(j : ℝ) + τ| ≤ (w : ℝ) / 10000 * t := by
  let a : ℝ := (w : ℝ) / 10000 * t
  simp only [lifts, Finset.mem_Icc, abs_le]
  change (-⌊a + τ⌋ ≤ j ∧ j ≤ ⌊a - τ⌋) ↔ -a ≤ (j : ℝ) + τ ∧ (j : ℝ) + τ ≤ a
  constructor
  · rintro ⟨h₁, h₂⟩
    have hj : -j ≤ ⌊a + τ⌋ := by omega
    have h := Int.le_floor.mp hj
    rw [Int.cast_neg] at h
    have h' := Int.le_floor.mp h₂
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have hj : -j ≤ ⌊a + τ⌋ := Int.le_floor.mpr (by rw [Int.cast_neg]; linarith)
    exact ⟨by omega, Int.le_floor.mpr (by linarith)⟩

theorem bandCount_eq_card (w : ℕ) {t : ℝ} (ht : 0 ≤ t) (τ : ℝ) :
    bandCount w t τ = ((lifts w t τ).card : ℤ) := by
  let a : ℝ := (w : ℝ) / 10000 * t
  have ha : 0 ≤ a := mul_nonneg (by positivity) ht
  have h : -⌊a + τ⌋ ≤ ⌊a - τ⌋ + 1 := by
    rw [← Int.ceil_neg]
    exact (Int.ceil_mono (show -(a + τ) ≤ a - τ by linarith)).trans (Int.ceil_le_floor_add_one _)
  change 1 + ⌊a - τ⌋ + ⌊a + τ⌋ = ((Finset.Icc (-⌊a + τ⌋) ⌊a - τ⌋).card : ℤ)
  rw [Int.card_Icc_of_le _ _ h]
  omega

noncomputable def rowRate (s : Shape) (i : ℕ) : ℝ := (s.rowUnits i : ℝ) / s.massUnit

noncomputable def rowCount (s : Shape) (t : ℝ) (i : ℕ) : ℤ := ⌊rowRate s i * t⌋

private theorem row_at_end (s : Shape) (i : ℕ) (e : Abscissa) :
    rowRate s i * e.value =
      (((s.rowUnits i : ℤ) * e.num : ℤ) : ℝ) / (((s.massUnit : ℤ) * e.den : ℤ) : ℝ) := by
  simp only [rowRate, Abscissa.value, Int.cast_mul, Int.cast_natCast, div_mul_div_comm]

theorem row_floor_of_between (s : Shape) (i : ℕ) (l r : Abscissa)
    (hs : 0 < s.massUnit) (hl : 0 < l.den) (hr : 0 < r.den)
    {x : ℝ} (hlo : rowRate s i * l.value ≤ x) (hhi : x < rowRate s i * r.value) :
    rowFloor s l i ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ rowStrictUpperFloor s r i := by
  have hd (e : Abscissa) (he : 0 < e.den) : 0 < (s.massUnit : ℤ) * e.den :=
    mul_pos (by exact_mod_cast hs) (by exact_mod_cast he)
  constructor
  · apply integer_lower_floor _ _ (hd l hl)
    rw [← row_at_end]
    exact hlo
  · apply integer_upper_floor _ _ (hd r hr)
    rw [← row_at_end]
    exact hhi

theorem row_count_between (s : Shape) (i : ℕ) (l r : Abscissa)
    (hs : 0 < s.massUnit) (hi : 0 < s.rowUnits i) (hl : 0 < l.den) (hr : 0 < r.den)
    {t : ℝ} (hlt : l.value ≤ t) (htr : t < r.value) :
    rowFloor s l i ≤ rowCount s t i ∧ rowCount s t i ≤ rowStrictUpperFloor s r i := by
  have hrate : 0 < rowRate s i := div_pos (by exact_mod_cast hi) (by exact_mod_cast hs)
  exact row_floor_of_between s i l r hs hl hr
    (mul_le_mul_of_nonneg_left hlt hrate.le) (mul_lt_mul_of_pos_left htr hrate)

private theorem sum_mono_on {α : Type*} (xs : List α) (f g : α → ℤ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

noncomputable def excessAt (s : Shape) (t τ : ℝ) : ℤ :=
  (s.widths.map (fun w => bandCount w t τ)).sum - (s.rows.map (rowCount s t)).sum

theorem excess_between (s : Shape) (l r : Abscissa) (b : Box)
    (hs : 0 < s.massUnit) (hrows : ∀ i ∈ s.rows, 0 < s.rowUnits i)
    (hl : 0 < l.den) (hr : 0 < r.den) {t τ : ℝ} (hlt : l.value ≤ t) (htr : t < r.value)
    (hbot : b.bottom.value t < τ) (htop : τ < b.top.value t) :
    lowerExcess s l r b ≤ excessAt s t τ ∧ excessAt s t τ ≤ upperExcess s l r b := by
  have bw (w : ℕ) := band_count_between l r b w hl hr hlt htr.le hbot htop
  have rw' (i : ℕ) (hi : i ∈ s.rows) := row_count_between s i l r hs (hrows i hi) hl hr hlt htr
  exact ⟨sub_le_sub (sum_mono_on _ _ _ (fun w _ => (bw w).1))
                    (sum_mono_on _ _ _ (fun i hi => (rw' i hi).2)),
         sub_le_sub (sum_mono_on _ _ _ (fun w _ => (bw w).2))
                    (sum_mono_on _ _ _ (fun i hi => (rw' i hi).1))⟩

theorem certified_gain_of_bounds (s : Shape) (l r : Abscissa) (b : Box) {x : ℤ}
    (hM : 0 < s.rows.length) (he : lowerExcess s l r b ≤ x ∧ x ≤ upperExcess s l r b)
    (hpass : dualPass s l r b = true) : 2 * (b.gain : ℤ) ≤ collisionTwice x s.rows.length := by
  have hd := of_decide_eq_true hpass
  have hmul : 2*b.dual * supportedExcess s l r b ≤ 2*b.dual * x := by
    by_cases hq : 0 ≤ b.dual
    · rw [supportedExcess, if_pos hq]
      exact mul_le_mul_of_nonneg_left he.1 (by omega)
    · rw [supportedExcess, if_neg hq]
      exact mul_le_mul_of_nonpos_left he.2 (by omega)
  exact (hd.trans (sub_le_sub_right hmul _)).trans
    (dual_le_collisionTwice _ _ _ (by exact_mod_cast hM))

theorem certified_gain (s : Shape) (l r : Abscissa) (b : Box)
    (hs : 0 < s.massUnit) (hrows : ∀ i ∈ s.rows, 0 < s.rowUnits i) (hM : 0 < s.rows.length)
    (hl : 0 < l.den) (hr : 0 < r.den) {t τ : ℝ} (hlt : l.value ≤ t) (htr : t < r.value)
    (hbot : b.bottom.value t < τ) (htop : τ < b.top.value t) (hpass : dualPass s l r b = true) :
    2 * (b.gain : ℤ) ≤ collisionTwice (excessAt s t τ) s.rows.length :=
  certified_gain_of_bounds s l r b hM
    (excess_between s l r b hs hrows hl hr hlt htr hbot htop) hpass

end PiPolynomialValues.PrimeWindow
