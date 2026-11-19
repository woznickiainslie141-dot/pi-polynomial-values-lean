module

public import OddPiPowers.PolynomialValues.Analysis.PrimitiveChord
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! Sum the interpolation error of a translated primitive over the
actual mesh. The singular cell is counted on each side of the edge. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Real

noncomputable def cellAllowance (h : ℝ) (j : ℕ) : ℝ := if j=0 then h/2 else h/(8*j)

theorem cellAllowance_nonneg {h : ℝ} (hh : 0≤h) (j : ℕ) : 0≤cellAllowance h j := by
  unfold cellAllowance
  split <;> positivity

theorem primitive_grid_cell {h u : ℝ} (hh : 0<h) (hu : 0≤u) (hu1 : u≤1) (j : ℕ) :
    |chord u (logPrimitive (j*h)) (logPrimitive ((j+1 : ℕ)*h))-logPrimitive (j*h+u*h)| ≤ cellAllowance h j := by
  cases j with
  | zero => simpa [cellAllowance] using primitive_chord_zero hh hu hu1
  | succ k =>
    have hp : 0<((k+1 : ℕ) : ℝ)*h := by positivity
    have H := primitive_chord_pos hp hh.le hu hu1
    have hd : h^2/(8*(((k+1 : ℕ) : ℝ)*h))=cellAllowance h (k+1) := by
      simp only [cellAllowance,Nat.succ_ne_zero,if_false]
      field_simp
      <;> ring
    rw [← hd]
    convert H using 2 <;> push_cast <;> ring_nf

theorem primitive_grid_negative {h u : ℝ} (hh : 0<h) (hu : 0≤u) (hu1 : u≤1) (j : ℕ) :
    |chord u (logPrimitive (-((j+1 : ℕ)*h))) (logPrimitive (-(j*h)))-
      logPrimitive (-((j+1 : ℕ)*h)+u*h)| ≤ cellAllowance h j := by
  have H := primitive_grid_cell hh (sub_nonneg.mpr hu1) (show 1-u≤1 by linarith) j
  have he : -(((j+1 : ℕ) : ℝ)*h)+u*h = -(j*h+(1-u)*h) := by push_cast; ring
  rw [he,logPrimitive_neg,logPrimitive_neg,logPrimitive_neg]
  rw [← abs_neg]
  convert H using 2
  unfold chord
  ring

def nearestCell (edge i : ℕ) : ℕ := if i<edge then edge-1-i else i-edge

theorem sum_nearestCell (f : ℕ → ℝ) (K edge : ℕ) (he : edge≤K) :
    (∑ i ∈ range K, f (nearestCell edge i)) =
      (∑ i ∈ range edge, f i)+∑ i ∈ range (K-edge), f i := by
  conv_lhs => rw [← Nat.add_sub_of_le he,sum_range_add]
  congr 1
  · rw [← sum_range_reflect f edge]
    apply sum_congr rfl
    intro i hi
    simp [nearestCell,mem_range.mp hi]
  · apply sum_congr rfl
    intro i _
    simp [nearestCell]

theorem cellAllowance_sum {h : ℝ} (hh : 0≤h) (K : ℕ) :
    (∑ i ∈ range K, cellAllowance h i) ≤ h/2+h/8*(1+Real.log (K : ℝ)) := by
  cases K with
  | zero => simp [Real.log_zero]; linarith
  | succ k =>
    have H := harmonic_le_one_add_log (k+1)
    rw [harmonic_eq_sum_Icc,Rat.cast_sum] at H
    simp only [Rat.cast_inv,Rat.cast_natCast] at H
    suffices he : (∑ i ∈ range (k+1), cellAllowance h i) ≤
        h/2+h/8*(∑ i ∈ Icc 1 (k+1), (i : ℝ)⁻¹) by
      exact he.trans (add_le_add_right (mul_le_mul_of_nonneg_left H (by positivity)) _)
    rw [sum_range_succ',cellAllowance,if_pos rfl,add_comm]
    apply add_le_add_right
    rw [mul_sum]
    have he : (∑ i ∈ range k, cellAllowance h (i+1)) =
        ∑ i ∈ Icc 1 k, h/8*(i : ℝ)⁻¹ := by
      rw [range_eq_Ico,← Ico_add_one_right_eq_Icc,← sum_Ico_add' (fun i : ℕ => h/8*(i : ℝ)⁻¹) 0 k (c := 1)]
      apply sum_congr rfl
      intro i _
      simp only [cellAllowance,Nat.succ_ne_zero,if_false]
      ring
    rw [he]
    apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.le_succ k))
    intros
    positivity

theorem total_chord_allowance {h : ℝ} (hh : 0≤h) {K edge : ℕ} (he : edge≤K) :
    h*(∑ i ∈ range K, cellAllowance h (nearestCell edge i)) ≤
      h^2*(5+Real.log K)/4 := by
  have H (j : ℕ) (hj : j≤K) : (∑ i ∈ range j, cellAllowance h i) ≤
      h/2+h/8*(1+Real.log K) :=
    (sum_le_sum_of_subset_of_nonneg (range_mono hj) (fun i _ _ => cellAllowance_nonneg hh i)).trans
      (cellAllowance_sum hh K)
  rw [sum_nearestCell _ _ _ he]
  have hb := mul_le_mul_of_nonneg_left (add_le_add (H edge he) (H (K-edge) (Nat.sub_le _ _))) hh
  linarith only [hb]

end PiPolynomialValues
