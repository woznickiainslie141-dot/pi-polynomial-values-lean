module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxFloor
public import OddPiPowers.PolynomialValues.Analysis.TailIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact normalized area of a certified strip after the change of variables
y = 1/t and z = yτ. Both residue signs enter through the factor two. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod MeasureTheory
open scoped Interval

noncomputable def Boundary.scaled (f : Boundary) (y : ℝ) : ℝ :=
  (f.slope : ℝ) / 10000 + (f.offset : ℝ) / 2 * y

theorem scaled_boundary (f : Boundary) (y : ℝ) (hy : y ≠ 0) :
    y * f.value y⁻¹ = f.scaled y := by
  unfold Boundary.value Boundary.scaled
  field_simp [hy] <;> ring

noncomputable def stripWidth (b : Box) (y : ℝ) : ℝ :=
  ((b.top.slope : ℝ) - b.bottom.slope) / 10000 +
    ((b.top.offset : ℝ) - b.bottom.offset) / 2 * y

theorem stripWidth_eq (b : Box) (y : ℝ) :
    stripWidth b y = b.top.scaled y - b.bottom.scaled y := by
  unfold stripWidth Boundary.scaled
  ring

noncomputable def weightedArea (s : Shape) (l r : Abscissa) (b : Box) : ℝ :=
  2 / (2 * (s.widths.sum : ℝ) / 10000) *
    (∫ y in r.value⁻¹..l.value⁻¹, stripWidth b y)

private theorem area_formula (w p q r s a b : ℝ) (hw : w ≠ 0) (hp : p ≠ 0) (hr : r ≠ 0) :
    2 / (2*w/10000) * ((q/p-s/r) * (a/10000 + b/2*(s/r+q/p)/2)) =
      ((q*r-p*s) * (4*a*(p*r)+10000*b*(q*r+p*s))) / (4*w*(p*r)^2) := by
  field_simp [hw, hp, hr] <;> ring

theorem weightedArea_eq_fraction (s : Shape) (l r : Abscissa) (b : Box)
    (hw : 0 < s.widths.sum) (hl : 0 < l.num) (hr : 0 < r.num) :
    weightedArea s l r b = (twiceAreaNum l r b : ℝ) / areaDen s l r := by
  simp only [weightedArea, stripWidth, integral_affine_real, Abscissa.value, inv_div,
    twiceAreaNum, areaDen, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_mul,
    Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  exact area_formula _ _ _ _ _ _ _ (Nat.cast_ne_zero.mpr hw.ne')
    (Nat.cast_ne_zero.mpr hl.ne') (Nat.cast_ne_zero.mpr hr.ne')

theorem credit_le_gain_mul_area (s : Shape) (l r : Abscissa) (b : Box)
    (hw : 0 < s.widths.sum) (hl : 0 < l.num) (hr : 0 < r.num) (hp : areaPass s l r b = true) :
    (b.credit : ℝ) / creditScale ≤ b.gain * weightedArea s l r b := by
  have ha : 0 < areaDen s l r := by unfold areaDen; positivity
  have hc : (0 : ℝ) < creditScale := by norm_num [creditScale]
  have hd : (b.credit : ℤ) * areaDen s l r ≤ (creditScale : ℤ) * b.gain * twiceAreaNum l r b :=
    of_decide_eq_true hp
  have hd' : (b.credit : ℝ) * areaDen s l r ≤
      (creditScale : ℝ) * b.gain * (twiceAreaNum l r b : ℝ) := by exact_mod_cast hd
  rw [weightedArea_eq_fraction s l r b hw hl hr, ← mul_div_assoc,
    div_le_div_iff₀ hc (by exact_mod_cast ha : (0 : ℝ) < areaDen s l r)]
  exact hd'.trans_eq (by ring)

end PiPolynomialValues.PrimeWindow
