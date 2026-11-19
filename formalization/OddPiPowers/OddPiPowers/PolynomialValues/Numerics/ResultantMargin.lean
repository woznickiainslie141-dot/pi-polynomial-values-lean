module

public import OddPiPowers.PolynomialValues.Numerics.RateData
public import OddPiPowers.PolynomialValues.PricedSimplex
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.Trigonometric

/-! The strict resultant margin holds on the entire interval of
secondary-root exponents. The scalar-path cost uses the actual
hyperbolic sine at the chosen interior radius. -/

@[expose] public section

namespace PiPolynomialValues

open Real

theorem sinh_le_geometric {x : ℝ} (h₀ : 0≤x) (h₁ : x<1) : sinh x≤x/(1-x^2) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp x).sub (NormedSpace.expSeries_div_hasSum_exp (-x))
  have ht := (hasSum_geometric_of_lt_one h₀ h₁).sub
    (hasSum_geometric_of_abs_lt_one (show |(-x)|<1 by simpa [abs_of_nonneg h₀] using h₁))
  have H := hasSum_le (fun n => by
    change x^n/(n.factorial : ℝ)-(-x)^n/(n.factorial : ℝ)≤x^n-(-x)^n
    rw [← sub_div]
    apply div_le_self (sub_nonneg.mpr ((le_abs_self ((-x)^n)).trans_eq (by rw [abs_pow,abs_neg,abs_of_nonneg h₀])))
    exact_mod_cast Nat.factorial_pos n) hs ht
  rw [← Real.exp_eq_exp_ℝ] at H
  have he : ((1-x)⁻¹-(1-(-x))⁻¹)/2=x/(1-x^2) := by
    have hA : 0<1-x := by linarith
    have hB : 0<1+x := by linarith
    rw [sub_neg_eq_add,show 1-x^2=(1-x)*(1+x) by ring]
    field_simp
    <;> ring
  rw [Real.sinh_eq,← he]
  exact div_le_div_of_nonneg_right H (by norm_num)

theorem scalar_sinh_rate {h x : ℝ} (hh : 0≤h) (hh' : h<1) (hx : 0≤x) (hxh : x≤h) :
    Real.sinh x≤x/(1-h^2) := by
  have hl := sq_lt_one_iff_abs_lt_one h |>.mpr (by simpa only [abs_of_nonneg hh] using hh')
  have hsq := pow_le_pow_left₀ hx hxh 2
  exact (sinh_le_geometric hx (hxh.trans_lt hh')).trans (div_le_div_of_nonneg_left hx (by linarith) (by linarith))

theorem RateData.resultant_margin (d : RateData) (margin : ℚ) (hp : d.passes margin)
    {y : ℝ} (hy : 0≤y) (hY : y≤(d.Y : ℝ)) :
    (d.auxDegree : ℝ)+(d.scale : ℝ)*d.cost-
      pricedMinimum (d.B : ℝ) ((d.target : ℝ)-y) (d.δ : ℝ)-(d.secondaryLower : ℝ)*y < -(margin : ℝ) := by
  obtain ⟨_,_,_,_,_,_,_,hB,_,_,_,_,_,hm,hg⟩ := hp
  have hB' : 0<(d.B : ℝ) := by exact_mod_cast hB
  have hl := priced_minimum_loss (B := (d.B : ℝ)) (C := (d.target : ℝ)) (δ := (d.δ : ℝ)) hB' hy hY
  have hm' := (Rat.cast_lt (K := ℝ)).mpr hm
  have hg' := (Rat.cast_lt (K := ℝ)).mpr hg
  change (margin : ℝ)<((d.B-(2*d.B-d.target-d.δ)^2/(8*d.B)-(d.auxDegree+d.scale*d.cost) : ℚ) : ℝ) at hm'
  change ((1/12 : ℚ) : ℝ)<((d.secondaryLower-d.loss : ℚ) : ℝ) at hg'
  push_cast at hm' hg'
  have he : (d.loss : ℝ)=(2*(d.B : ℝ)-d.target+d.Y-d.δ)/(4*d.B) := by
    unfold RateData.loss
    push_cast
    rfl
  rw [← he] at hl
  have hh : 0≤((d.secondaryLower : ℝ)-d.loss)*y := mul_nonneg (by linarith only [hg']) hy
  unfold pricedMinimum at hl ⊢
  linarith only [hm',hl,hh]

theorem quadratic_resultant_margin {y : ℝ} (hy : 0≤y) (hY : y≤(quadraticRateData.Y : ℝ)) :
    (quadraticRateData.auxDegree : ℝ)+(quadraticRateData.scale : ℝ)*quadraticRateData.cost-
      pricedMinimum (quadraticRateData.B : ℝ) ((quadraticRateData.target : ℝ)-y) (quadraticRateData.δ : ℝ)-
        (quadraticRateData.secondaryLower : ℝ)*y < -(8/100000000 : ℝ) := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using quadraticRateData.resultant_margin _ quadratic_rate_tests hy hY

theorem cubic_resultant_margin {y : ℝ} (hy : 0≤y) (hY : y≤(cubicRateData.Y : ℝ)) :
    (cubicRateData.auxDegree : ℝ)+(cubicRateData.scale : ℝ)*cubicRateData.cost-
      pricedMinimum (cubicRateData.B : ℝ) ((cubicRateData.target : ℝ)-y) (cubicRateData.δ : ℝ)-
        (cubicRateData.secondaryLower : ℝ)*y < -(11/100000000 : ℝ) := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using cubicRateData.resultant_margin _ cubic_rate_tests hy hY

end PiPolynomialValues
