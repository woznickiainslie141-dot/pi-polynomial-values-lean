module

public import OddPiPowers.PolynomialValues.Numerics.PackedConvolution
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Group the exact energy of a signed mesh charge by positive lag.
Opposite orientations have the same weight. No diagonal term occurs
because the second primitive vanishes at zero. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

theorem strict_tail_shift {A : Type*} [AddCommMonoid A] (n i : ℕ) (hi : i<n) (f : ℕ → A) :
    (∑ j ∈ range n, if i<j then f j else 0) =
    ∑ k ∈ range n, if i+1+k<n then f (i+1+k) else 0 := by
  have h : i+1+(n-(i+1))=n := by omega
  have h' : (n-(i+1))+(i+1)=n := by omega
  calc
    _ = (∑ j ∈ range (i+1), if i<j then f j else 0)+
          ∑ j ∈ range (n-(i+1)), if i<i+1+j then f (i+1+j) else 0 := by
      rw [← sum_range_add,h]
    _ = ∑ j ∈ range (n-(i+1)), f (i+1+j) := by
      rw [sum_eq_zero (fun j hj => if_neg (by have := mem_range.mp hj; omega)),zero_add]
      apply sum_congr rfl
      intro j _
      rw [if_pos (by omega)]
    _ = ∑ k ∈ range n, if i+1+k<n then f (i+1+k) else 0 := by
      nth_rw 2 [← h']
      rw [sum_range_add]
      have hz : (∑ j ∈ range (i+1), if i+1+(n-(i+1)+j)<n then f (i+1+(n-(i+1)+j)) else 0)=0 :=
        sum_eq_zero (fun _ _ => if_neg (by omega))
      rw [hz,add_zero]
      apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega)]

def positiveLag (n : ℕ) (a : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ range n, if i+1+k<n then a i*a (i+1+k) else 0

theorem positiveLag_convolution (n : ℕ) (a : ℕ → ℤ) (k : ℕ) :
    meshConvolution n n a (fun j => a (n-1-j)) (n+k)=positiveLag n a k := by
  unfold meshConvolution positiveLag
  rw [← sum_range_reflect (fun j => (if j≤n+k ∧ n+k-j<n then a (n+k-j) else 0)*a (n-1-j)) n]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have h₁ : n+k-(n-1-j)=j+1+k := by omega
  have h₂ : n-1-(n-1-j)=j := by omega
  rw [h₁,h₂]
  by_cases h : j+1+k<n <;> simp [h,show n-1-j≤n+k by omega,mul_comm]

theorem mesh_energy_lags (n : ℕ) (d : ℕ → ℤ) (J : ℕ → ℝ) (h0 : J 0=0) :
    (∑ i ∈ range n, ∑ j ∈ range n, (d i : ℝ)*d j*J ((i : ℤ)-j).natAbs) =
      ∑ k ∈ range n, (2*(positiveLag n d k : ℝ))*J (k+1) := by
  let F (i j : ℕ) := (d i : ℝ)*d j*J ((i : ℤ)-j).natAbs
  let G (i j : ℕ) := if i<j then F i j else 0
  have hs (i j : ℕ) : F i j=F j i := by
    dsimp [F]
    rw [show ((i : ℤ)-j).natAbs=((j : ℤ)-i).natAbs by omega,mul_comm (d i : ℝ)]
  have HG (i j : ℕ) : F i j=G i j+G j i := by
    rcases lt_trichotomy i j with h|h|h
    · simp [G,h,h.not_gt]
    · subst j; simp [G,F,h0]
    · simp [G,h,h.not_gt,hs i j]
  have HGsum : (∑ i ∈ range n, ∑ j ∈ range n, G i j) =
      ∑ k ∈ range n, (positiveLag n d k : ℝ)*J (k+1) := by
    calc
      _ = ∑ i ∈ range n, ∑ k ∈ range n, if i+1+k<n then F i (i+1+k) else 0 :=
        sum_congr rfl (fun i hi => strict_tail_shift n i (mem_range.mp hi) (F i))
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro k _
        simp only [positiveLag,Int.cast_sum,sum_mul]
        apply sum_congr rfl
        intro i _
        by_cases h : i+1+k<n
        · have he : ((i : ℤ)-((i+1+k : ℕ) : ℤ)).natAbs=k+1 := by omega
          simp only [if_pos h,F,he,Int.cast_ite,Int.cast_mul]
        · simp [h]
  change (∑ i ∈ range n, ∑ j ∈ range n, F i j)=_
  simp_rw [HG]
  simp only [sum_add_distrib]
  rw [show (∑ i ∈ range n, ∑ j ∈ range n, G j i)=(∑ i ∈ range n, ∑ j ∈ range n, G i j) from sum_comm,HGsum,
    ← two_mul,mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem signed_primitive_allowance (v f : ℤ) (E : ℝ) (hl : (f : ℝ)≤E) (hu : E≤(f : ℝ)+2) :
    (v : ℝ)*E≤((v*f+2*max 0 v : ℤ) : ℝ) := by
  by_cases h : 0≤v
  · rw [max_eq_right h]
    push_cast
    have H := mul_le_mul_of_nonneg_left hu (show (0 : ℝ)≤v by exact_mod_cast h)
    linarith
  · rw [max_eq_left (le_of_not_ge h)]
    push_cast
    simpa only [mul_zero,add_zero] using mul_le_mul_of_nonpos_left hl
      (show (v : ℝ)≤0 by exact_mod_cast (le_of_not_ge h))

end PiPolynomialValues
