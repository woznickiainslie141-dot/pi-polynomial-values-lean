module

public import OddPiPowers.PolynomialValues.Analysis.PathMoment
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! An analytic correction that takes the prescribed value at the
interior radius. Its absolute imaginary part has asymptotically optimal
Poisson cost as the correction parameter tends to one. -/

@[expose] public section

namespace PiPolynomialValues

open Complex Metric Real Set
open scoped ComplexConjugate

noncomputable def correctionFactor (r t : ℝ) (z : ℂ) : ℂ := ((r⁻¹+t*r : ℝ) : ℂ)/(1+(t : ℂ)*z^2)
noncomputable def correctionPath (r t : ℝ) (z : ℂ) : ℂ := z*correctionFactor r t z

theorem correctionFactor_analytic {t : ℝ} (ht : 0≤t) (ht1 : t<1) (r : ℝ) :
    AnalyticOnNhd ℂ (correctionFactor r t) (closedBall 0 1) := by
  intro z hz
  have hn : ‖z‖≤1 := by simpa [mem_closedBall,dist_eq_norm] using hz
  have hlt : ‖(t : ℂ)*z^2‖<1 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
    exact (mul_le_of_le_one_right ht (pow_le_one₀ (norm_nonneg _) hn)).trans_lt ht1
  apply analyticAt_const.div (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2)))
  intro he
  change 1+(t : ℂ)*z^2=0 at he
  have h : (t : ℂ)*z^2= -1 := by linear_combination he
  simp [h] at hlt

@[simp] theorem correctionPath_zero (r t : ℝ) : correctionPath r t 0=0 := by simp [correctionPath]

theorem correctionPath_radius {r t : ℝ} (hr : 0<r) (ht : 0≤t) :
    correctionPath r t (r : ℂ)=1 := by
  have h : 1+t*r^2≠0 := by positivity
  have hr' : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : 1+(t : ℂ)*(r : ℂ)^2≠0 := by exact_mod_cast h
  rw [correctionPath,correctionFactor,← mul_div_assoc,div_eq_one_iff_eq he]
  push_cast
  field_simp [hr']
  <;> ring

theorem correctionPath_im {z : ℂ} (hz : ‖z‖=1) (r t : ℝ) :
    (correctionPath r t z).im = (r⁻¹+t*r)*(1-t)*z.im/((1-t)^2+4*t*z.re^2) := by
  have h0 : z ≠ 0 := by intro he; simp [he] at hz
  have h1 : z*conj z=1 := by rw [Complex.mul_conj,← Complex.sq_norm,hz]; norm_num
  have hn := Complex.sq_norm z
  rw [hz,one_pow,Complex.normSq_apply] at hn
  have hden : 1+(t : ℂ)*z^2=z*(conj z+(t : ℂ)*z) := by rw [mul_add,h1]; ring
  have he : correctionPath r t z=((r⁻¹+t*r : ℝ) : ℂ)/(conj z+(t : ℂ)*z) := by
    rw [correctionPath,correctionFactor,hden,← mul_div_assoc,mul_div_mul_left _ _ h0]
  have hs : normSq (conj z+(t : ℂ)*z)=(1-t)^2+4*t*z.re^2 := by
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    nlinarith only [hn,congrArg (fun x : ℝ => t*x) hn,congrArg (fun x : ℝ => t^2*x) hn]
  rw [he,Complex.div_im,hs]
  simp only [Complex.ofReal_im,Complex.ofReal_re,zero_mul,zero_div,zero_sub,Complex.add_im,
    Complex.conj_im,Complex.mul_im,add_zero,zero_mul]
  ring

theorem correctionPath_absolute_error {r t : ℝ} (hr : 0<r) (ht : 0<t) (ht1 : t<1)
    {z : ℂ} (hz : ‖z‖=1) :
    |(correctionPath r t z).im|-(correctionPath r t z).im*z.im ≤ (r⁻¹+t*r)*(1-t)/(4*t) := by
  let C := (r⁻¹+t*r)*(1-t)
  let D := (1-t)^2+4*t*z.re^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hs := Complex.abs_im_le_norm z
  rw [hz] at hs
  have hn := Complex.sq_norm z
  rw [hz,one_pow,Complex.normSq_apply] at hn
  have hd : (|z.im|-z.im^2)/D ≤ 1/(4*t) := by
    apply (div_le_div_iff₀ hD (by positivity)).mpr
    dsimp [D]
    have H : |z.im|-z.im^2 ≤ z.re^2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right H (show 0≤4*t by positivity),sq_nonneg (1-t)]
  rw [correctionPath_im hz]
  change |C*z.im/D|-(C*z.im/D)*z.im ≤ C/(4*t)
  rw [abs_div,abs_of_pos hD,abs_mul,abs_of_nonneg hC]
  convert mul_le_mul_of_nonneg_left hd hC using 1 <;> ring

end PiPolynomialValues
