module

public import OddPiPowers.PolynomialValues.MahlerHeight
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Normalize every conjugate by the same factor as in the Mahler measure.
The truncation at one has a uniform cost at every root. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

noncomputable def rootScale (z : ℂ) : ℝ := max 1 ‖z‖

theorem one_le_rootScale (z : ℂ) : 1 ≤ rootScale z := le_max_left _ _

theorem rootScale_pos (z : ℂ) : 0 < rootScale z := zero_lt_one.trans_le (one_le_rootScale _)

noncomputable def relativeDistance (ξ z : ℂ) : ℝ := ‖ξ - z‖ / rootScale z
noncomputable def truncatedDistance (ξ z : ℂ) : ℝ := min 1 (relativeDistance ξ z)

theorem relativeDistance_nonneg (ξ z : ℂ) : 0 ≤ relativeDistance ξ z :=
  div_nonneg (norm_nonneg _) (rootScale_pos z).le

theorem relativeDistance_le (ξ z : ℂ) : relativeDistance ξ z ≤ 1 + ‖ξ‖ := by
  apply (div_le_iff₀ (rootScale_pos z)).mpr
  calc
    _ ≤ ‖ξ‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ ‖ξ‖ * rootScale z + rootScale z := add_le_add
      (le_mul_of_one_le_right (norm_nonneg _) (one_le_rootScale z)) (le_max_right _ _)
    _ = _ := by ring

theorem truncatedDistance_nonneg (ξ z : ℂ) : 0 ≤ truncatedDistance ξ z :=
  le_min zero_le_one (relativeDistance_nonneg _ _)

theorem relativeDistance_le_mul_truncated (ξ z : ℂ) :
    relativeDistance ξ z ≤ (1 + ‖ξ‖) * truncatedDistance ξ z := by
  rcases le_total (relativeDistance ξ z) 1 with h | h
  · rw [truncatedDistance, min_eq_right h]
    exact le_mul_of_one_le_left (relativeDistance_nonneg _ _) (by linarith [norm_nonneg ξ])
  · rw [truncatedDistance, min_eq_left h, mul_one]
    exact relativeDistance_le _ _

/-- Two normalized differences are controlled by the worse ordered root. -/
theorem root_pair_distance_le (ξ x y : ℂ) (h : truncatedDistance ξ x ≤ truncatedDistance ξ y) :
    ‖x - y‖ ≤ rootScale x * rootScale y * (2 * (1 + ‖ξ‖) * truncatedDistance ξ y) := by
  have hb : 0 ≤ 1 + ‖ξ‖ := by positivity
  have hx : ‖ξ - x‖ ≤ rootScale x * ((1 + ‖ξ‖) * truncatedDistance ξ y) := by
    have h1 := (relativeDistance_le_mul_truncated ξ x).trans (mul_le_mul_of_nonneg_left h hb)
    simpa only [mul_comm (rootScale x)] using (div_le_iff₀ (rootScale_pos x)).mp h1
  have hy : ‖ξ - y‖ ≤ rootScale y * ((1 + ‖ξ‖) * truncatedDistance ξ y) := by
    simpa only [mul_comm (rootScale y)] using
      (div_le_iff₀ (rootScale_pos y)).mp (relativeDistance_le_mul_truncated ξ y)
  have hxy : rootScale x ≤ rootScale x * rootScale y :=
    le_mul_of_one_le_right (rootScale_pos x).le (one_le_rootScale y)
  have hyx : rootScale y ≤ rootScale x * rootScale y :=
    le_mul_of_one_le_left (rootScale_pos y).le (one_le_rootScale x)
  have hpos := mul_nonneg hb (truncatedDistance_nonneg ξ y)
  calc
    _ ≤ ‖x - ξ‖ + ‖ξ - y‖ := by
      simpa only [dist_eq_norm] using dist_triangle x ξ y
    _ = ‖ξ - x‖ + ‖ξ - y‖ := by rw [norm_sub_rev x ξ]
    _ ≤ _ := (add_le_add hx hy).trans (by
      have h1 := mul_le_mul_of_nonneg_right hxy hpos
      have h2 := mul_le_mul_of_nonneg_right hyx hpos
      linarith only [h1, h2])

private theorem scale_product (S : Multiset ℂ) (ξ : ℂ) :
    (S.map rootScale).prod * (S.map (relativeDistance ξ)).prod =
      (S.map (fun z => ‖ξ - z‖)).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have hz : rootScale z * relativeDistance ξ z = ‖ξ - z‖ := by
      unfold relativeDistance
      field_simp [(rootScale_pos z).ne']
    calc
      _ = (rootScale z * relativeDistance ξ z) *
          ((S.map rootScale).prod * (S.map (relativeDistance ξ)).prod) := by ring
      _ = _ := by rw [hz, ih]

/-- Exact factored evaluation on all conjugates, with multiplicity. -/
theorem norm_eval_eq_measure_mul_relative (p : ℤ[X]) (ξ : ℂ) :
    ‖p.eval₂ (Int.castRingHom ℂ) ξ‖ = measure p *
      ((p.map (Int.castRingHom ℂ)).roots.map (relativeDistance ξ)).prod := by
  let f := p.map (Int.castRingHom ℂ)
  change ‖p.eval₂ (Int.castRingHom ℂ) ξ‖ = f.mahlerMeasure * _
  rw [← eval_map, (IsAlgClosed.splits f).eval_eq_prod_roots, norm_mul,
    Multiset.norm_prod_map, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_assoc]
  congr 1
  exact (scale_product f.roots ξ).symm

end PiPolynomialValues
