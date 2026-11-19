module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxSound
public import Mathlib.Data.List.Forall2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Direct integer-frequency membership and stable row floors for the
actual prefix lengths on a trimmed prime window. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

theorem actual_band_membership (w N p : ℕ) (hp : 0 < p) (r j : ℤ) :
    j ∈ lifts w ((N : ℝ)/p) ((r : ℝ)/p) ↔
      |j * (p : ℤ) + r| * 10000 ≤ (w : ℤ)*N := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hj : (j : ℝ)+(r : ℝ)/p = ((j : ℝ)*p+r)/p := by field_simp [hp'.ne'] <;> ring
  have hw : (w : ℝ)/10000*((N : ℝ)/p) = ((w : ℝ)*N/10000)/p := by ring
  rw [mem_lifts, hj, hw, abs_div, abs_of_pos hp', div_le_div_iff_of_pos_right hp',
    le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)]
  constructor <;> intro h <;> exact_mod_cast h

theorem actual_row_floor (s : Shape) (i : ℕ) (l r : Abscissa)
    (hs : 0 < s.massUnit) (hi : 0 < s.rowUnits i) (hl : 0 < l.den) (hr : 0 < r.den)
    (m N p : ℕ) (hp : 0 < p) (K δ : ℝ)
    (hlt : l.value+δ ≤ (N : ℝ)/p) (htr : (N : ℝ)/p ≤ r.value-δ)
    (herr : |(m : ℝ)-rowRate s i*N| ≤ K) (hsmall : K < rowRate s i*δ*p) :
    rowFloor s l i ≤ ((m/p : ℕ) : ℤ) ∧ ((m/p : ℕ) : ℤ) ≤ rowStrictUpperFloor s r i := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 < rowRate s i := div_pos (by exact_mod_cast hi) (by exact_mod_cast hs)
  have h : |(m : ℝ)/p - rowRate s i*((N : ℝ)/p)| < rowRate s i*δ := by
    rw [← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hp', div_lt_iff₀ hp']
    exact herr.trans_lt hsmall
  have e := abs_lt.mp h
  have h₁ := mul_le_mul_of_nonneg_left hlt ha.le
  have h₂ := mul_le_mul_of_nonneg_left htr ha.le
  have limits := row_floor_of_between s i l r hs hl hr (x := (m : ℝ)/p)
    (by linarith only [e.1, h₁]) (by linarith only [e.2, h₂])
  simpa only [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div] using limits

/-- Equal row ratios can have different actual prefix lengths. Pair the
ordered lists, preserving all copies. -/
theorem row_sums_of_paired_bounds {α β : Type*} (f g : α → ℤ) (u : β → ℤ)
    {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun a b => f a ≤ u b ∧ u b ≤ g a) xs ys) :
    (xs.map f).sum ≤ (ys.map u).sum ∧ (ys.map u).sum ≤ (xs.map g).sum := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    exact ⟨add_le_add hab.1 ih.1, add_le_add hab.2 ih.2⟩

end PiPolynomialValues.PrimeWindow
