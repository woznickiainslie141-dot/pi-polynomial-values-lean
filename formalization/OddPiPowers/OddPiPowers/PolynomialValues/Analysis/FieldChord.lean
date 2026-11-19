module

public import OddPiPowers.PolynomialValues.Analysis.MeshChordError

/-! Simultaneous chord enclosure for all fields on an entire mesh cell.
The common error sums the largest jump at each density edge. -/

@[expose] public section

namespace PiPolynomialValues

open Real Finset

theorem edge_chord_error {h u : ℝ} (hh : 0<h) (hu : 0≤u) (hu1 : u≤1) (i e : ℕ) :
    |chord u (logPrimitive ((i : ℝ)*h-e*h)) (logPrimitive (((i : ℝ)+1)*h-e*h))-
      logPrimitive ((i : ℝ)*h+u*h-e*h)| ≤ cellAllowance h (nearestCell e i) := by
  by_cases he : e ≤ i
  · have H := primitive_grid_cell hh hu hu1 (i-e)
    have z : ((i-e : ℕ) : ℝ)=(i : ℝ)-e := Nat.cast_sub he
    have h0 : ((i-e : ℕ) : ℝ)*h=i*h-e*h := by rw [z]; ring
    have h1 : ((i-e+1 : ℕ) : ℝ)*h=((i : ℝ)+1)*h-e*h := by rw [Nat.cast_succ,z]; ring
    have h2 : ((i-e : ℕ) : ℝ)*h+u*h=i*h+u*h-e*h := by rw [h0]; ring
    rw [h2,h0,h1] at H
    simpa only [nearestCell,if_neg (not_lt.mpr he)] using H
  · have hi : i < e := by omega
    let j := e-1-i
    have hj : j+1+i=e := by dsimp [j]; omega
    have hcast : (j : ℝ)+1+i=e := by exact_mod_cast hj
    have he1 : -(j*h) = ((i : ℝ)+1)*h-e*h := by linear_combination -h*hcast
    have he0 : -(((j+1 : ℕ) : ℝ)*h) = (i : ℝ)*h-e*h := by push_cast; linear_combination -h*hcast
    have he2 : -(((j+1 : ℕ) : ℝ)*h)+u*h = (i : ℝ)*h+u*h-e*h := by rw [he0]; ring
    have H := primitive_grid_negative hh hu hu1 j
    rw [he2,he0,he1] at H
    simpa only [nearestCell,if_pos hi] using H

variable {ι : Type*} [Fintype ι]

noncomputable def meshField (h slope offset : ℝ) (e : ι → ℕ) (d : ι → ℝ) (x : ℝ) :=
  slope*x+offset+∑ k, d k*logPrimitive (x-e k*h)

theorem meshField_chord {h u : ℝ} (hh : 0<h) (hu : 0≤u) (hu1 : u≤1) (i : ℕ)
    (e : ι → ℕ) (d B : ι → ℝ) (hB : ∀ k, |d k|≤B k) (s b l r : ℝ)
    (hl : meshField h s b e d (i*h)≤l) (hr : meshField h s b e d (((i : ℝ)+1)*h)≤r) :
    meshField h s b e d (i*h+u*h) ≤ chord u l r + ∑ k, B k*cellAllowance h (nearestCell (e k) i) := by
  let F := meshField h s b e d
  let D (k : ι) := logPrimitive (i*h+u*h-e k*h)-
    chord u (logPrimitive (i*h-e k*h)) (logPrimitive (((i : ℝ)+1)*h-e k*h))
  have he : F (i*h+u*h)-chord u (F (i*h)) (F (((i : ℝ)+1)*h)) = ∑ k, d k*D k := by
    have ht (k : ι) : d k*D k = d k*logPrimitive (i*h+u*h-e k*h)-
        (1-u)*(d k*logPrimitive (i*h-e k*h))-u*(d k*logPrimitive (((i : ℝ)+1)*h-e k*h)) := by
      unfold D chord
      ring
    simp only [ht,sum_sub_distrib,← mul_sum,F,meshField,chord]
    ring
  have hc : chord u (F (i*h)) (F (((i : ℝ)+1)*h)) ≤ chord u l r :=
    add_le_add (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hu1)) (mul_le_mul_of_nonneg_left hr hu)
  have H : (∑ k, d k*D k) ≤ ∑ k, B k*cellAllowance h (nearestCell (e k) i) := by
    apply sum_le_sum
    intro k _
    have hd : |D k|≤cellAllowance h (nearestCell (e k) i) := by
      dsimp only [D]
      rw [abs_sub_comm]
      exact edge_chord_error hh hu hu1 i (e k)
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul (hB k) hd
      (abs_nonneg _) ((abs_nonneg _).trans (hB k))))
  change F (i*h+u*h) ≤ _
  linarith

end PiPolynomialValues
