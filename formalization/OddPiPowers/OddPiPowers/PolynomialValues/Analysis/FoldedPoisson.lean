module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Direct arc increments for the Poisson density folded into a quadrant. -/

@[expose] public section

namespace PiPolynomialValues

open MeasureTheory Real

noncomputable def foldStretch (z : ℝ) : ℝ := (1+z^2)/(1-z^2)

noncomputable def foldNorm (g t : ℝ) : ℝ := cos t ^ 2 + g^2 * sin t ^ 2

noncomputable def foldedPoisson (z t : ℝ) : ℝ :=
  (2 / π) * ((1-z^4) / ((1-z^2)^2+4*z^2*sin t ^ 2))

noncomputable def foldDot (g a t : ℝ) : ℝ :=
  cos a * cos t + (g^2 * sin a) * sin t

noncomputable def foldCross (g a t : ℝ) : ℝ :=
  (g * cos a) * sin t - (g * sin a) * cos t

theorem foldNorm_pos {g : ℝ} (hg : 0 < g) (t : ℝ) : 0 < foldNorm g t := by
  by_cases h : sin t = 0
  · have he : cos t ^ 2 = 1 := by
      simpa only [h, zero_pow (by decide : 2 ≠ 0), zero_add] using sin_sq_add_cos_sq t
    rw [foldNorm, h, he]
    norm_num
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sq_pos_of_pos hg) (sq_pos_of_ne_zero h))

theorem foldStretch_pos {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : 0 < foldStretch z :=
  div_pos (by positivity) (by nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)])

theorem foldedPoisson_stretch {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (t : ℝ) :
    foldedPoisson z t = (2/π) * (foldStretch z / foldNorm (foldStretch z) t) := by
  have hm : 0 < 1-z^2 := by nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)]
  have hd : 0 < (1-z^2)^2+4*z^2*sin t^2 := by positivity
  have he : foldNorm (foldStretch z) t * (1-z^2)^2 = (1-z^2)^2+4*z^2*sin t^2 := by
    calc
      _ = cos t ^ 2 * (1-z^2)^2 + (1+z^2)^2 * sin t ^ 2 := by
        unfold foldNorm foldStretch
        rw [add_mul]
        congr 1
        field_simp [hm.ne']
      _ = _ := by linear_combination (1-z^2)^2 * (sin_sq_add_cos_sq t)
  unfold foldedPoisson
  congr 1
  rw [div_eq_div_iff hd.ne' (foldNorm_pos (foldStretch_pos hz hz1) t).ne']
  calc
    _ = (1+z^2)/(1-z^2) * (foldNorm (foldStretch z) t * (1-z^2)^2) := by
      field_simp [hm.ne']
      ring
    _ = _ := by rw [he]; rfl

private theorem atan_ratio_factor (C D U : ℝ) (hD : D ≠ 0) :
    (1/(1+(C/D)^2)) * (U/D^2) = U/(D^2+C^2) := by
  have hs : 0 < D^2+C^2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hD) (sq_nonneg _)
  have ht : 0 < 1+(C/D)^2 := by positivity
  field_simp [hD, hs.ne', ht.ne']

theorem hasDerivAt_foldAngle {g : ℝ} (hg : 0 < g) (a t : ℝ)
    (hd : foldDot g a t ≠ 0) :
    HasDerivAt (fun x => arctan (foldCross g a x / foldDot g a x)) (g/foldNorm g t) t := by
  let C' := (g*cos a)*cos t-(g*sin a)*(-sin t)
  let D' := cos a*(-sin t)+(g^2*sin a)*cos t
  have hc : HasDerivAt (foldCross g a) C' t :=
    ((hasDerivAt_sin t).const_mul (g*cos a)).sub ((hasDerivAt_cos t).const_mul (g*sin a))
  have hdot : HasDerivAt (foldDot g a) D' t :=
    ((hasDerivAt_cos t).const_mul (cos a)).add ((hasDerivAt_sin t).const_mul (g^2*sin a))
  have hsize : foldDot g a t ^ 2 + foldCross g a t ^ 2 = foldNorm g a * foldNorm g t := by
    unfold foldDot foldCross foldNorm
    ring
  have hdet : C'*foldDot g a t - foldCross g a t*D' = g*foldNorm g a := by
    calc
      _ = (g*foldNorm g a)*(sin t ^ 2 + cos t ^ 2) := by
        dsimp [C', D', foldDot, foldCross, foldNorm]
        ring
      _ = _ := by rw [sin_sq_add_cos_sq, mul_one]
  apply ((hc.div hdot hd).arctan).congr_deriv
  simp only [Pi.div_apply]
  rw [atan_ratio_factor _ _ _ hd, hdet, hsize]
  field_simp [(foldNorm_pos hg a).ne', (foldNorm_pos hg t).ne']

theorem integral_foldedPoisson_arc {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (a b : ℝ)
    (hd : ∀ t ∈ Set.uIcc a b, foldDot (foldStretch z) a t ≠ 0) :
    (∫ t in a..b, foldedPoisson z t) =
      (2/π) * arctan (foldCross (foldStretch z) a b / foldDot (foldStretch z) a b) := by
  let g := foldStretch z
  have hg : 0 < g := foldStretch_pos hz hz1
  have hcont : Continuous (fun t => (2/π)*(g/foldNorm g t)) :=
    continuous_const.mul (continuous_const.div (by unfold foldNorm; fun_prop)
      (fun t => (foldNorm_pos hg t).ne'))
  have hc : foldCross g a a = 0 := by unfold foldCross; ring
  calc
    _ = ∫ t in a..b, (2/π)*(g/foldNorm g t) :=
      intervalIntegral.integral_congr (fun t _ => foldedPoisson_stretch hz hz1 t)
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => (hasDerivAt_foldAngle hg a t (hd t ht)).const_mul (2/π))
        (hcont.intervalIntegrable _ _), hc]
      simp [g]

end PiPolynomialValues
