module

public import OddPiPowers.PolynomialValues.Numerics.PoissonArc
public import Mathlib.Data.Rat.BigOperators

/-! A rational test for one angular cell, with both integral enclosures
transferred to the actual real integrals on that cell. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory

structure ArcRow where
  left : ℚ
  right : ℚ
  massLo : ℚ
  massHi : ℚ
  sineLo : ℚ
  sineHi : ℚ
deriving DecidableEq

def arcChain (left right : ℚ) : List ArcRow → Bool
  | [] => decide (left = right)
  | e :: es => decide (left = e.left ∧ e.left < e.right) && arcChain e.right right es

private def arcInequalities {K : Type*} [Field K] [LE K] [LT K]
    (x y a b c pl ph wl wh jl jh : K) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧ y < 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧
    wl ≤ 2*a/ph ∧ 2*(a+x^21/21)/pl ≤ wh ∧
    jl ≤ c*b/ph ∧ c*(b+y^17/(17*(1-y^2)))/pl ≤ jh

def ArcRow.passes (z : ℚ) (e : ArcRow) : Bool := by
  let x := arcMassArg z e.left e.right
  let y := arcSineArg z e.left e.right
  let a := arcOdd (-1) 10 x
  let b := arcOdd 1 8 y
  exact decide (0 < z ∧ z < 1 ∧ 0 ≤ e.left ∧ e.left ≤ e.right ∧ e.right ≤ 1 ∧
    (0 < e.left ∨ e.right < 1) ∧ 0 ≤ x ∧ 0 ≤ y ∧ y < 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧
    e.massLo ≤ 2*a/(314159265358979323847 / 10^20) ∧
    2*(a+x^21/21)/(314159265358979323846 / 10^20) ≤ e.massHi ∧
    e.sineLo ≤ ((1-z^2)/z)*b/(314159265358979323847 / 10^20) ∧
    ((1-z^2)/z)*(b+y^17/(17*(1-y^2)))/(314159265358979323846 / 10^20) ≤ e.sineHi)

private theorem inequalities_cast (x y a b c pl ph wl wh jl jh : ℚ)
    (h : arcInequalities x y a b c pl ph wl wh jl jh) :
    arcInequalities (x : ℝ) y a b c pl ph wl wh jl jh := by
  unfold arcInequalities at h ⊢
  exact_mod_cast h

private theorem cast_massArg (z l r : ℚ) :
    ((arcMassArg z l r : ℚ) : ℝ) = arcMassArg (z : ℝ) (l : ℝ) (r : ℝ) := by
  unfold arcMassArg halfAngleSin halfAngleCos
  push_cast
  rfl

private theorem cast_sineArg (z l r : ℚ) :
    ((arcSineArg z l r : ℚ) : ℝ) = arcSineArg (z : ℝ) (l : ℝ) (r : ℝ) := by
  unfold arcSineArg halfAngleCos
  push_cast
  rfl

private theorem cast_arcOdd (s : ℚ) (n : ℕ) (x : ℚ) :
    ((arcOdd s n x : ℚ) : ℝ) = arcOdd (s : ℝ) n (x : ℝ) := by
  unfold arcOdd
  push_cast
  rfl

def ArcRow.enclosed (z : ℚ) (e : ArcRow) : Prop :=
  (∫ t in (2*arctan e.left)..(2*arctan e.right), foldedPoisson z t) ∈
    Set.Icc (e.massLo : ℝ) (e.massHi : ℝ) ∧
  (∫ t in (2*arctan e.left)..(2*arctan e.right), foldedPoisson z t * sin t) ∈
    Set.Icc (e.sineLo : ℝ) (e.sineHi : ℝ)

theorem ArcRow.enclosed_of_passes (z : ℚ) (e : ArcRow) (h : e.passes z = true) : e.enclosed z := by
  let x := arcMassArg z e.left e.right
  let y := arcSineArg z e.left e.right
  obtain ⟨hz, hz', hl, hlr, hr, hs, hq⟩ := of_decide_eq_true h
  apply arcChecks_sound (by exact_mod_cast hz) (by exact_mod_cast hz') (by exact_mod_cast hl)
    (by exact_mod_cast hlr) (by exact_mod_cast hr) (by exact_mod_cast hs)
  have hh := inequalities_cast x y (arcOdd (-1) 10 x) (arcOdd 1 8 y) ((1-z^2)/z)
    (314159265358979323846 / 10^20) (314159265358979323847 / 10^20)
    e.massLo e.massHi e.sineLo e.sineHi hq
  simpa only [arcChecks, arcInequalities, x, y, arcPiLo, arcPiHi, cast_arcOdd, cast_massArg,
    cast_sineArg, Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_ofNat] using hh

end PiPolynomialValues
