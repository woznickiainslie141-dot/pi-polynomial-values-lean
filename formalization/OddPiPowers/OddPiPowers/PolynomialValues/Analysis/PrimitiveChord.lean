module

public import OddPiPowers.PolynomialValues.Analysis.LogPrimitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A uniform interpolation estimate for the signed logarithmic
primitive, including mesh cells that touch its singularity. -/

@[expose] public section

namespace PiPolynomialValues

open Real Set

noncomputable def chord (u a b : ℝ) := (1-u)*a+u*b

theorem chord_affine (u s k a b : ℝ) :
    chord u (s*a+k) (s*b+k) = s*chord u a b+k := by unfold chord; ring

theorem logPrimitive_neg (x : ℝ) : logPrimitive (-x) = -logPrimitive x := by
  simp [logPrimitive,log_neg_eq_log]
  <;> ring

theorem neg_mul_log_half {u : ℝ} (hu : 0 ≤ u) : -(u*log u) ≤ 1/2 := by
  let s := Real.sqrt u
  have hs : 0 ≤ s := sqrt_nonneg _
  have hsq : s^2=u := sq_sqrt hu
  have hh := mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log hs) hs
  rw [← hsq,Real.log_pow]
  push_cast
  nlinarith [sq_nonneg (s-1/2)]

theorem primitive_chord_zero {h u : ℝ} (hh : 0<h) (hu : 0≤u) (hu1 : u≤1) :
    |chord u (logPrimitive 0) (logPrimitive h)-logPrimitive (u*h)| ≤ h/2 := by
  have he : chord u (logPrimitive 0) (logPrimitive h)-logPrimitive (u*h) = h*(-(u*log u)) := by
    by_cases hz : u=0
    · simp [hz,chord,logPrimitive]
    · unfold chord logPrimitive
      rw [log_mul hz hh.ne']
      ring
  have h0 : 0≤ -(u*log u) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hu (log_nonpos hu hu1))
  rw [he,abs_of_nonneg (mul_nonneg hh.le h0)]
  linarith [mul_le_mul_of_nonneg_left (neg_mul_log_half hu) hh.le]

theorem mulLog_quadratic_concave {a : ℝ} (ha : 0<a) :
    ConcaveOn ℝ (Ici a) (fun x : ℝ => x*log x-x^2/(2*a)) := by
  let f' (x : ℝ) := log x+1-x/a
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici a)
    (continuous_mul_log.sub ((continuous_id.pow 2).div_const _)).continuousOn (f' := f') (f'' := fun x => x⁻¹-a⁻¹)
  · intro x hx
    have hax : a ≤ x := interior_subset hx
    have hd := (hasDerivAt_mul_log (ha.trans_le hax).ne').sub (((hasDerivAt_id x).pow 2).div_const (2*a))
    apply HasDerivAt.hasDerivWithinAt
    convert hd using 1
    dsimp [f']
    field_simp
    <;> ring
  · intro x hx
    have hax : a ≤ x := interior_subset hx
    have hd := ((hasDerivAt_log (ha.trans_le hax).ne').add_const 1).sub ((hasDerivAt_id x).div_const a)
    simpa [f',one_div,Pi.sub_def] using hd.hasDerivWithinAt (s := interior (Ici a))
  · intro x hx
    exact sub_nonpos.mpr (inv_anti₀ ha (interior_subset hx))

theorem primitive_chord_pos {a h u : ℝ} (ha : 0<a) (hh : 0≤h) (hu : 0≤u) (hu1 : u≤1) :
    |chord u (logPrimitive a) (logPrimitive (a+h))-logPrimitive (a+u*h)| ≤ h^2/(8*a) := by
  let f (x : ℝ) := x*log x
  let D := chord u (f a) (f (a+h))-f (a+u*h)
  have hd : chord u (logPrimitive a) (logPrimitive (a+h))-logPrimitive (a+u*h)=D := by
    dsimp [D,chord,f,logPrimitive]
    ring
  have hsum : 1-u+u=1 := by ring
  have hpt : (1-u)*a+u*(a+h)=a+u*h := by ring
  have h0 := Real.convexOn_mul_log.2 ha.le (add_nonneg ha.le hh) (sub_nonneg.mpr hu1) hu hsum
  have hA := (mulLog_quadratic_concave ha).2 (le_refl a) (le_add_of_nonneg_right hh) (sub_nonneg.mpr hu1) hu hsum
  simp only [smul_eq_mul,hpt] at h0 hA
  have hD : 0≤D := sub_nonneg.mpr h0
  rw [hd,abs_of_nonneg hD]
  change (1-u)*(a*log a)+u*((a+h)*log (a+h))-(a+u*h)*log (a+u*h) ≤ h^2/(8*a)
  field_simp [ha.ne'] at hA ⊢
  nlinarith only [hA,sq_nonneg ((2*u-1)*h)]

end PiPolynomialValues
