module

public import OddPiPowers.PolynomialValues.Numerics.PrimeTailData
public import OddPiPowers.PolynomialValues.Analysis.TailIntegral
public import Mathlib.Data.Rat.BigOperators

/-! Each rational credit integrates the actual signed column and row tails.
A restriction to one interval at a given level gives a lower bound on its
positive-part integral over a larger window. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open MeasureTheory
open scoped Interval

noncomputable def TailTerm.value (e : TailTerm) (h : ℕ) (y : ℝ) : ℝ :=
  max 0 ((e.width : ℝ) - ((h-e.grade : ℕ) : ℝ)*y)

private theorem TailTerm.continuous_value (e : TailTerm) (h : ℕ) : Continuous (e.value h) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))

theorem TailTerm.integral_value (e : TailTerm) (h : ℕ) (l r : ℚ) (hlr : l ≤ r) :
    (∫ y in (l : ℝ)..(r : ℝ), e.value h y) = (e.area h l r : ℝ) := by
  have hw : 0 ≤ e.width := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let k := h-e.grade
  change (∫ y in (l : ℝ)..(r : ℝ), max 0 ((e.width : ℝ)-(k : ℝ)*y)) =
    (rampIntegral e.width k l r : ℝ)
  rw [integral_tail_real _ _ _ _ (by exact_mod_cast hw) (Nat.cast_nonneg _) (by exact_mod_cast hlr)]
  by_cases hk : k = 0
  · simp [tailIntegralReal, rampIntegral, hk]
  · simp [tailIntegralReal, rampIntegral, hk, Nat.cast_ne_zero.mpr hk, Rat.cast_max]

noncomputable def listTail (S : List TailTerm) (h : ℕ) (y : ℝ) : ℝ :=
  (S.map (fun e => e.value h y)).sum

private theorem continuous_listTail (S : List TailTerm) (h : ℕ) : Continuous (listTail S h) := by
  induction S with
  | nil => exact continuous_const
  | cons e S ih => exact (e.continuous_value h).add ih

private theorem integral_listTail (S : List TailTerm) (h : ℕ) (l r : ℚ) (hlr : l ≤ r) :
    (∫ y in (l : ℝ)..(r : ℝ), listTail S h y) = (((S.map (fun e => e.area h l r)).sum : ℚ) : ℝ) := by
  induction S with
  | nil => simp [listTail]
  | cons e S ih =>
    change (∫ y in (l : ℝ)..(r : ℝ), e.value h y + listTail S h y) =
      ((e.area h l r + (S.map (fun a => a.area h l r)).sum : ℚ) : ℝ)
    rw [intervalIntegral.integral_add ((e.continuous_value h).intervalIntegrable _ _)
      ((continuous_listTail S h).intervalIntegrable _ _), e.integral_value h l r hlr, ih, Rat.cast_add]

noncomputable def Shape.netTailValue (s : Shape) (h : ℕ) (y : ℝ) : ℝ :=
  (4 * listTail s.columnTails h y - listTail s.rowTails h y) / (s.totalWidthQ : ℝ)

theorem Shape.continuous_netTailValue (s : Shape) (h : ℕ) : Continuous (s.netTailValue h) :=
  ((continuous_const.mul (continuous_listTail s.columnTails h)).sub
    (continuous_listTail s.rowTails h)).div_const _

theorem Shape.integral_netTailValue (s : Shape) (h : ℕ) (l r : ℚ) (hlr : l ≤ r) :
    (∫ y in (l : ℝ)..(r : ℝ), s.netTailValue h y) = (s.netTailIntegral h l r : ℝ) := by
  unfold Shape.netTailValue Shape.netTailIntegral
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (f := fun y : ℝ => 4 * listTail s.columnTails h y) (g := listTail s.rowTails h)
    ((continuous_const.mul (continuous_listTail s.columnTails h)).intervalIntegrable _ _)
    ((continuous_listTail s.rowTails h).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_listTail _ h l r hlr, integral_listTail _ h l r hlr]
  push_cast <;> rfl

theorem Shape.netTailIntegral_le_positive_part (s : Shape) (h : ℕ) (l r : ℚ) {a b : ℝ}
    (ha : a ≤ l) (hlr : l ≤ r) (hb : (r : ℝ) ≤ b) :
    (s.netTailIntegral h l r : ℝ) ≤ ∫ y in a..b, max 0 (s.netTailValue h y) := by
  rw [← s.integral_netTailValue h l r hlr]
  have hlr' : (l : ℝ) ≤ r := by exact_mod_cast hlr
  have hc := s.continuous_netTailValue h
  have hpos : Continuous (fun y => max 0 (s.netTailValue h y)) := continuous_const.max hc
  exact (intervalIntegral.integral_mono_on hlr' (hc.intervalIntegrable _ _)
      (hpos.intervalIntegrable _ _) (fun y _ => le_max_right _ _)).trans
    (intervalIntegral.integral_mono_interval ha hlr' hb
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _)) (hpos.intervalIntegrable _ _))

end PiPolynomialValues.FourPeriod
