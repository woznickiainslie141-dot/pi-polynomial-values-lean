module

public import OddPiPowers.PolynomialValues.Numerics.ShapeGeometry
public import OddPiPowers.PolynomialValues.FourPeriod.SelectedPolynomial
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Choose the actual integer scale as a multiple of four. All signed
band cells then align at their integer endpoints while the mass scale
still tends to the requested multiple of the logarithmic height. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Real Filter
open scoped Topology

noncomputable def rootScaleIndex (s : Shape) (b X : ℝ) := 4*⌊(b/(4*s.massUnit))*X⌋₊

theorem rootScaleIndex_tendsto {ι : Type*} {F : Filter ι} {X : ι → ℝ} (hX : Tendsto X F atTop)
    (s : Shape) (hs : 0<s.massUnit) {b : ℝ} (hb : 0<b) :
    Tendsto (fun i => rootScaleIndex s b (X i)) F atTop := by
  have ha : 0<b/(4*s.massUnit) := by positivity
  have h := tendsto_nat_floor_atTop.comp ((hX.const_mul_atTop ha))
  exact h.const_mul_atTop' (by decide : 0<4)

theorem rootScaleIndex_ratio {ι : Type*} {F : Filter ι} {X : ι → ℝ} (hX : Tendsto X F atTop)
    (s : Shape) (hs : 0<s.massUnit) {b : ℝ} (hb : 0<b) :
    Tendsto (fun i => ((s.massUnit*rootScaleIndex s b (X i) : ℕ) : ℝ)/X i) F (𝓝 b) := by
  let a : ℝ := b/(4*s.massUnit)
  have ha : 0<a := by dsimp [a]; positivity
  have h := ((tendsto_nat_floor_mul_div_atTop ha.le).comp hX).const_mul ((s.massUnit : ℝ)*4)
  rw [show (s.massUnit : ℝ)*4*a=b by dsimp [a]; field_simp [Nat.cast_ne_zero.mpr hs.ne']] at h
  apply h.congr
  intro i
  change (s.massUnit : ℝ)*4*((⌊a*X i⌋₊ : ℝ)/X i)=_
  simp only [rootScaleIndex,Nat.cast_mul,Nat.cast_ofNat]
  dsimp only [a]
  ring

theorem rootScaleIndex_grid (s : Shape) (b X : ℝ) :
    s.massUnit*rootScaleIndex s b X =
      40000*(s.rows.sum*⌊(b/(4*s.massUnit))*X⌋₊) := by
  unfold rootScaleIndex Shape.massUnit
  ring

theorem affine_ratio_atTop (a b c d : ℕ) (hc : 0<c) :
    Tendsto (fun t : ℕ => ((a*t+b : ℕ) : ℝ)/((c*t+d : ℕ) : ℝ)) atTop (𝓝 ((a:ℝ)/c)) := by
  have hi : Tendsto (fun t : ℕ => ((t : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := (hi.const_mul (b : ℝ)).const_add (a : ℝ)
  have hd := (hi.const_mul (d : ℝ)).const_add (c : ℝ)
  simp only [mul_zero,add_zero] at hn hd
  apply (hn.div hd (Nat.cast_ne_zero.mpr hc.ne')).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  simp only [Pi.div_apply,Nat.cast_add,Nat.cast_mul]
  have h : (t : ℝ)≠0 := Nat.cast_ne_zero.mpr ht.ne'
  have hn : 0<(c : ℝ)*t+d := by positivity
  field_simp [h,hn.ne']
  <;> ring

end PiPolynomialValues.FourPeriod
