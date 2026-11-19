module

public import OddPiPowers.PolynomialValues.Analysis.FoldedPoisson
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! An exact logarithmic primitive for the sine-weighted folded Poisson arc. -/

@[expose] public section

namespace PiPolynomialValues

open Real MeasureTheory

noncomputable def halfLogRatio (x : ℝ) : ℝ := (log (1+x)-log (1-x))/2
noncomputable def foldCosScale (z : ℝ) : ℝ := 2*z/(1+z^2)

theorem hasDerivAt_halfLogRatio {x : ℝ} (hl : -1 < x) (hr : x < 1) :
    HasDerivAt halfLogRatio (1/(1-x^2)) x := by
  have hp : 1+x ≠ 0 := by linarith
  have hm : 1-x ≠ 0 := by linarith
  have hs : 1-x^2 ≠ 0 := by
    have : 0 < (1-x)*(1+x) := mul_pos (by linarith) (by linarith)
    nlinarith
  have h₁ : HasDerivAt (fun y : ℝ => 1+y) 1 x := (hasDerivAt_id x).const_add 1
  have h₂ : HasDerivAt (fun y : ℝ => 1-y) (-1) x := (hasDerivAt_id x).const_sub 1
  apply (((h₁.log hp).sub (h₂.log hm)).div_const 2).congr_deriv
  field_simp [hp, hm, hs] <;> ring

theorem halfLogRatio_sub {u v : ℝ} (hul : -1 < u) (hur : u < 1)
    (hvl : -1 < v) (hvr : v < 1) (hd : 1-u*v ≠ 0) :
    halfLogRatio u - halfLogRatio v = halfLogRatio ((u-v)/(1-u*v)) := by
  have hu₁ : 1+u ≠ 0 := by linarith
  have hu₂ : 1-u ≠ 0 := by linarith
  have hv₁ : 1+v ≠ 0 := by linarith
  have hv₂ : 1-v ≠ 0 := by linarith
  have h₁ : 1+(u-v)/(1-u*v) = (1+u)*(1-v)/(1-u*v) := by field_simp [hd] <;> ring
  have h₂ : 1-(u-v)/(1-u*v) = (1-u)*(1+v)/(1-u*v) := by field_simp [hd] <;> ring
  unfold halfLogRatio
  rw [h₁, h₂, log_div (mul_ne_zero hu₁ hv₂) hd, log_div (mul_ne_zero hu₂ hv₁) hd,
    log_mul hu₁ hv₂, log_mul hu₂ hv₁]
  ring

theorem foldCosScale_mem {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    0 < foldCosScale z ∧ foldCosScale z < 1 := by
  have hp : 0 < 1+z^2 := by positivity
  constructor
  · exact div_pos (by positivity) hp
  · apply (div_lt_one hp).mpr
    nlinarith [sq_pos_of_pos (sub_pos.mpr hz1)]

private theorem scale_cos_range {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (t : ℝ) :
    -1 < k*cos t ∧ k*cos t < 1 := by
  constructor
  · have h := mul_le_mul_of_nonneg_left (neg_one_le_cos t) hk.le
    linarith
  · have h := mul_le_mul_of_nonneg_left (cos_le_one t) hk.le
    linarith

private theorem foldSine_deriv {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (t : ℝ) :
    HasDerivAt (fun x => (-(1-z^2)/(π*z))*halfLogRatio (foldCosScale z*cos x))
      (foldedPoisson z t * sin t) t := by
  let k := foldCosScale z
  obtain ⟨hk,hk1⟩ := foldCosScale_mem hz hz1
  obtain ⟨hl,hr⟩ := scale_cos_range hk hk1 t
  have h : HasDerivAt (fun x => k*cos x) (k*(-sin t)) t := (hasDerivAt_cos t).const_mul k
  have hm : 0 < 1-z^2 := by nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)]
  have hp : 0 < 1+z^2 := by positivity
  have hD : 0 < (1-z^2)^2+4*z^2*sin t ^ 2 := by positivity
  have he : (1-z^2)^2+4*z^2*sin t ^ 2 = (1+z^2)^2-(2*z*cos t)^2 := by
    linear_combination 4*z^2 * (sin_sq_add_cos_sq t)
  have hf : 1-(k*cos t)^2 = ((1-z^2)^2+4*z^2*sin t ^ 2)/(1+z^2)^2 := by
    rw [he]
    dsimp [k, foldCosScale]
    field_simp [hp.ne'] <;> ring
  apply (((hasDerivAt_halfLogRatio hl hr).comp t h).const_mul (-(1-z^2)/(π*z))).congr_deriv
  change (-(1-z^2)/(π*z)) * ((1/(1-(k*cos t)^2))*(k*(-sin t))) = _
  rw [hf]
  unfold foldedPoisson
  dsimp [k, foldCosScale]
  field_simp [Real.pi_ne_zero, hz.ne', hp.ne', hD.ne'] <;> ring

theorem integral_foldedPoisson_sine_arc {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (a b : ℝ) :
    (∫ t in a..b, foldedPoisson z t * sin t) =
      (1-z^2)/(π*z) * halfLogRatio
        ((foldCosScale z*cos a-foldCosScale z*cos b) /
          (1-(foldCosScale z*cos a)*(foldCosScale z*cos b))) := by
  let k := foldCosScale z
  obtain ⟨hk,hk1⟩ := foldCosScale_mem hz hz1
  obtain ⟨ha,ha'⟩ := scale_cos_range hk hk1 a
  obtain ⟨hb,hb'⟩ := scale_cos_range hk hk1 b
  have hd : 1-(k*cos a)*(k*cos b) ≠ 0 := by
    have hab : |k * cos a| * |k * cos b| < 1 := by
      calc
        _ ≤ |k * cos a| * 1 := mul_le_mul_of_nonneg_left (abs_lt.mpr ⟨hb,hb'⟩).le (abs_nonneg _)
        _ < 1 := by simpa using (abs_lt.mpr ⟨ha,ha'⟩ : |k*cos a| < 1)
    rw [← abs_mul] at hab
    linarith [(abs_lt.mp hab).2]
  have hm : 0 < 1-z^2 := by nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)]
  have hc : Continuous (fun t => foldedPoisson z t * sin t) := by
    unfold foldedPoisson
    apply Continuous.mul _ continuous_sin
    exact continuous_const.mul (continuous_const.div (by fun_prop) (fun t => by positivity))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => foldSine_deriv hz hz1 t)
    (hc.intervalIntegrable a b), ← halfLogRatio_sub ha ha' hb hb' hd]
  ring

end PiPolynomialValues
