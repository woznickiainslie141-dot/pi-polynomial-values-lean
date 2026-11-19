module

public import OddPiPowers.PolynomialValues.Analysis.RadialFourier
public import OddPiPowers.PolynomialValues.Analysis.LogPrimitives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Order.ProjIcc

/-! Uniform estimates for the radial logarithm in the real frequency
coordinate. The only exceptional point is the diagonal itself. -/

@[expose] public section

namespace PiPolynomialValues

open Real
open scoped ComplexConjugate

abbrev FrequencyInterval := Set.Icc (-1 : ℝ) 1

noncomputable def frequencyProjection : C(ℝ,FrequencyInterval) :=
  ⟨Set.projIcc (-1 : ℝ) 1 (by norm_num),continuous_projIcc⟩

noncomputable def unitFrequency : C(FrequencyInterval,ℂ) :=
  ⟨fun x => Complex.exp ((Real.arccos x : ℂ)*Complex.I),by fun_prop⟩

theorem unitFrequency_norm (x : FrequencyInterval) : ‖unitFrequency x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem unitFrequency_re (x : FrequencyInterval) : (unitFrequency x).re = x := by
  change (Complex.exp ((Real.arccos x : ℂ)*Complex.I)).re = _
  rw [Complex.exp_ofReal_mul_I_re,Real.cos_arccos x.2.1 x.2.2]

noncomputable def logSmoothing (q d : ℝ) := log (|d|+q)-log |d|

theorem radialPair_upper {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    radialPair r u v ≤ 2*|u.re-v.re|+4*(1-r) := by
  let c (s : ℝ) (z : ℂ) := ‖1-(s : ℂ)*z‖
  have hdiff (z : ℂ) (hz : ‖z‖ = 1) : c r z-c 1 z ≤ 1-r := by
    have h := norm_sub_norm_le (1-(r : ℂ)*z) (1-1*z)
    rw [show 1-(r : ℂ)*z-(1-1*z) = ((1-r : ℝ) : ℂ)*z by push_cast; ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hr1),hz,mul_one] at h
    simpa [c] using h
  have hbound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) : c s z ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) ((s : ℂ)*z)
    simp only [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs,hz,mul_one] at h
    exact h.trans (by linarith)
  let a := u*v
  let b := u*conj v
  have ha : ‖a‖ = 1 := by simp [a,norm_mul,hu,hv]
  have hb : ‖b‖ = 1 := by simp [b,norm_mul,hu,hv]
  have h₁ := mul_le_mul_of_nonneg_right (hdiff a ha) (show 0 ≤ c r b from norm_nonneg _)
  have h₂ := mul_le_mul_of_nonneg_left (hdiff b hb) (show 0 ≤ c 1 a from norm_nonneg _)
  have he : 2*|u.re-v.re| = c 1 a*c 1 b := by simpa [c,a,b] using two_abs_real_sub_of_unit hu hv
  rw [he]
  change c r a*c r b ≤ _
  nlinarith only [h₁,h₂,mul_le_mul_of_nonneg_left (hbound r hr hr1 b hb) (sub_nonneg.mpr hr1),
    mul_le_mul_of_nonneg_right (hbound 1 zero_le_one le_rfl a ha) (sub_nonneg.mpr hr1)]

theorem radial_log_error {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hd : u.re ≠ v.re)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    log r ≤ log (radialPair r u v) - frequencyLog (u.re-v.re) ∧
    log (radialPair r u v) - frequencyLog (u.re-v.re) ≤ logSmoothing (2*(1-r)) (u.re-v.re) := by
  let d := |u.re-v.re|
  have hd' : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hd)
  have hl := regularized_pair_bound hu hv hr hr1 (ε := 0) le_rfl
  simp only [add_zero,mul_zero,zero_div,zero_add,one_div] at hl
  have hm : r*(2*d) ≤ radialPair r u v := by
    have hh := mul_le_mul_of_nonneg_left hl hr.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hh
  have hp := radialPair_pos hr.le hr1 hu hv
  have hq : 0 < d+2*(1-r) := by linarith
  rw [frequencyLog_of_ne (sub_ne_zero.mpr hd)]
  change log r ≤ log (radialPair r u v)-log (2*d) ∧
    log (radialPair r u v)-log (2*d) ≤ log (d+2*(1-r))-log d
  constructor
  · have hh := log_le_log (mul_pos hr (by positivity)) hm
    rw [log_mul hr.ne' (by positivity)] at hh
    linarith
  · have hh := log_le_log hp ((radialPair_upper hu hv hr.le hr1.le).trans_eq
      (show 2*d+4*(1-r) = 2*(d+2*(1-r)) by ring))
    rw [log_mul (by norm_num) hq.ne'] at hh
    rw [log_mul (by norm_num) hd'.ne']
    linarith

end PiPolynomialValues
