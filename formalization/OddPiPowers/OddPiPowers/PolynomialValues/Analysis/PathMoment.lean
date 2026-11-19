module

public import OddPiPowers.PolynomialValues.Analysis.PoissonComparison
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The sine moment of an analytic path that vanishes at zero fixes its
interior value. This also applies to the rational correction path. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Metric Real
open scoped ComplexConjugate

theorem poissonMean_congr {w : ℂ} {f g : ℂ → ℝ} (he : Set.EqOn f g (sphere 0 1)) :
    poissonMean w f = poissonMean w g := by
  apply circleAverage_congr_sphere
  intro z hz
  exact congrArg (fun t : ℝ => unitPoisson w z*t) (he (by simpa using hz))

theorem complex_sine_product {z a : ℂ} (hz : ‖z‖=1) :
    (z*a).im*z.im = ((a-z*(z*a))/2).re := by
  have hn := Complex.sq_norm z
  rw [hz,one_pow,Complex.normSq_apply] at hn
  simp [Complex.div_ofNat_re,Complex.sub_re,Complex.mul_re,Complex.mul_im]
  nlinarith only [congrArg (fun x : ℝ => a.re*x) hn]

theorem path_sine_moment {r : ℝ} (hr : 0<r) (hr1 : r<1) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1)) :
    poissonMean (r : ℂ) (fun z => (z*H z).im*z.im) =
      (r⁻¹-r)*(r*H (r : ℂ)).re/2 := by
  let A (z : ℂ) := (H z-z*(z*H z))/2
  have ha : AnalyticOnNhd ℂ A (closedBall 0 1) := fun z hz =>
    ((hH z hz).sub (analyticAt_id.mul (analyticAt_id.mul (hH z hz)))).div_const
  have hw : ‖(r : ℂ)‖<1 := by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr1
  have he : poissonMean (r : ℂ) (fun z => (z*H z).im*z.im) =
      poissonMean (r : ℂ) (fun z => (A z).re) := by
    apply poissonMean_congr
    intro z hz
    exact complex_sine_product (by simpa [mem_sphere,dist_eq_norm] using hz)
  rw [he,poissonMean_re hw ha]
  simp [A,Complex.div_ofNat_re,Complex.sub_re,Complex.mul_re]
  field_simp [hr.ne']
  <;> ring

end PiPolynomialValues
