module

public import OddPiPowers.PolynomialValues.Analysis.UniformGridIntegral
public import OddPiPowers.PolynomialValues.FourPeriod.Columns
public import OddPiPowers.PolynomialValues.FourPeriod.ShapeUnits
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The complete integer bands, with both endpoints included, converge
against every continuous test. Different derivative layers can use
different tests before their limits are added. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Filter
open scoped Topology Interval

theorem signedBand_grid (B : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    (∑ t : ↥(Icc (-(B : ℤ)) (B : ℤ)), f ((t.val : ℝ)*h)) =
      (∑ k ∈ range (2*B), f (-((B : ℝ)*h)+k*h))+f ((B : ℝ)*h) := by
  rw [(Icc (-(B : ℤ)) (B : ℤ)).sum_coe_sort (fun t : ℤ => f ((t : ℝ)*h)),Int.Icc_eq_finset_map,sum_map]
  rw [show ((B : ℤ)+1-(-(B : ℤ))).toNat = 2*B+1 by omega,sum_range_succ]
  simp only [Function.Embedding.trans_apply,Nat.castEmbedding_apply,addLeftEmbedding_apply,
    Int.cast_add,Int.cast_neg,Int.cast_natCast]
  congr 1
  · apply sum_congr rfl
    intro k _
    congr 1
    ring
  · congr 1
    push_cast
    ring

theorem band_test_limit (B N : ℕ) (hN : 0 < N) (f : C(ℝ,ℝ)) :
    Tendsto (fun t : ℕ => (((N*t : ℕ) : ℝ)⁻¹)*
      ∑ x : ↥(Icc (-((B*t : ℕ) : ℤ)) ((B*t : ℕ) : ℤ)), f ((x.val : ℝ)*((N*t : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 (∫ z in -((B : ℝ)/N)..((B : ℝ)/N), f z)) := by
  let h (t : ℕ) := ((N*t : ℕ) : ℝ)⁻¹
  let b := (B : ℝ)/N
  have hp : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hu : Tendsto h atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' hN))
  have he : ∀ᶠ t in atTop, ((B*t : ℕ) : ℝ)*h t = b := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [h,b,Nat.cast_mul]
    field_simp
  have hm : ∀ᶠ t in atTop, ((2*(B*t) : ℕ) : ℝ)*h t=b-(-b) := by
    filter_upwards [he] with t ht
    push_cast at ht ⊢
    linarith
  have H := left_grid_integral_limit f (-b) b (fun t => 2*(B*t)) h (fun _ => by dsimp [h]; positivity)
    hu (by dsimp [b]; linarith [show (0 : ℝ) ≤ (B : ℝ)/N by positivity]) hm
  have HC := H.add (hu.mul_const (f b))
  simp only [zero_mul,add_zero] at HC
  apply HC.congr'
  filter_upwards [he] with t ht
  rw [signedBand_grid]
  change h t*(∑ k ∈ range (2*(B*t)), f (-b+k*h t))+h t*f b =
    h t*((∑ k ∈ range (2*(B*t)), f (-(((B*t : ℕ) : ℝ)*h t)+k*h t))+f (((B*t : ℕ) : ℝ)*h t))
  rw [ht,mul_add]

theorem shape_layer_integral_limit (s : Shape) (hN : 0 < s.massUnit)
    (f : Fin s.widths.length → C(ℝ,ℝ)) :
    Tendsto (fun t : ℕ => ((s.massUnit*t : ℕ) : ℝ)⁻¹*
      ∑ c : Column (s.band t), f c.1 ((c.2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 (∑ j, ∫ z in -((s.widths.get j : ℝ)/10000)..((s.widths.get j : ℝ)/10000), f j z)) := by
  have hrow : (s.rows.sum : ℝ) ≠ 0 := by
    have : s.rows.sum ≠ 0 := fun h => by simp [Shape.massUnit,h] at hN
    exact Nat.cast_ne_zero.mpr this
  have hj (j : Fin s.widths.length) :
      (↑(s.widths.get j*s.rows.sum) : ℝ)/s.massUnit = (s.widths.get j : ℝ)/10000 := by
    simp only [Shape.massUnit,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  have HH := tendsto_finsetSum (univ : Finset (Fin s.widths.length))
    (fun j _ => band_test_limit (s.widths.get j*s.rows.sum) s.massUnit hN (f j))
  simp_rw [hj] at HH
  apply HH.congr'
  filter_upwards with t
  rw [Fintype.sum_sigma,mul_sum]
  rfl

end PiPolynomialValues.FourPeriod
