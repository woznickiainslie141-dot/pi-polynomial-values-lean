module

public import OddPiPowers.PolynomialValues.Analysis.ArcCoordinates
public import OddPiPowers.PolynomialValues.Analysis.OddSeriesBounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sufficient finite inequalities for both integrals on a complete arc. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory

noncomputable def arcPiLo : ℝ := 314159265358979323846 / 10^20
noncomputable def arcPiHi : ℝ := 314159265358979323847 / 10^20

def arcChecks (z l r wl wh jl jh : ℝ) : Prop :=
  let x := arcMassArg z l r
  let y := arcSineArg z l r
  let a := arcOdd (-1) 10 x
  let b := arcOdd 1 8 y
  let c := (1-z^2)/z
  0 ≤ x ∧ 0 ≤ y ∧ y < 1 ∧ 0 ≤ a ∧ 0 ≤ b ∧
    wl ≤ 2*a/arcPiHi ∧ 2*(a+x^21/21)/arcPiLo ≤ wh ∧
    jl ≤ c*b/arcPiHi ∧ c*(b+y^17/(17*(1-y^2)))/arcPiLo ≤ jh

private theorem between_pi_bounds {c a x b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hl : a ≤ x) (hu : x ≤ b) : c*a/arcPiHi ≤ c*x/π ∧ c*x/π ≤ c*b/arcPiLo := by
  have hlo : 0 < arcPiLo := by norm_num [arcPiLo]
  have hp : arcPiLo ≤ π := by convert Real.pi_gt_d20.le using 1 <;> norm_num [arcPiLo]
  have hq : π ≤ arcPiHi := by convert Real.pi_lt_d20.le using 1 <;> norm_num [arcPiHi]
  constructor
  · exact (div_le_div_of_nonneg_left (mul_nonneg hc ha) pi_pos hq).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hc) pi_pos.le)
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu hc) pi_pos.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hc ((ha.trans hl).trans hu)) hlo hp)

theorem arcChecks_sound {z l r wl wh jl jh : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hs : 0 < l ∨ r < 1)
    (hc : arcChecks z l r wl wh jl jh) :
    (∫ t in (2*arctan l)..(2*arctan r), foldedPoisson z t) ∈ Set.Icc wl wh ∧
    (∫ t in (2*arctan l)..(2*arctan r), foldedPoisson z t*sin t) ∈ Set.Icc jl jh := by
  obtain ⟨hx,hy,hy1,ha,hb,h₁,h₂,h₃,h₄⟩ := hc
  obtain ⟨wa,wb⟩ := arctan_ten_bounds hx
  obtain ⟨ja,jb⟩ := halfLogRatio_odd_bounds hy hy1 8
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] at jb
  have hc₀ : 0 ≤ (1-z^2)/z := div_nonneg (by
    nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)]) hz.le
  obtain ⟨hw,hw'⟩ := between_pi_bounds (by norm_num : (0:ℝ) ≤ 2) ha wa wb
  obtain ⟨hj,hj'⟩ := between_pi_bounds hc₀ hb ja jb
  obtain ⟨hW,hJ⟩ := foldedPoisson_halfAngle_integrals hz hz1 hl hlr hr hs
  have eW : (2/π)*arctan (arcMassArg z l r) = 2*arctan (arcMassArg z l r)/π := by ring
  have eJ : (1-z^2)/(π*z)*halfLogRatio (arcSineArg z l r) =
      ((1-z^2)/z)*halfLogRatio (arcSineArg z l r)/π := by
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  rw [hW,hJ,eW,eJ]
  exact ⟨⟨h₁.trans hw,hw'.trans h₂⟩,⟨h₃.trans hj,hj'.trans h₄⟩⟩

end PiPolynomialValues
