module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Complex.Basic

/-! Uniform evaluation of bounded-degree polynomials on any fixed finite set,
from bounds on the disk of radius two. -/

@[expose] public section

namespace PiPolynomialValues

open Polynomial

/-- At fixed degree and at a fixed finite set of points, extrapolation outside
the disk costs a factor independent of the coefficients and of the disk bound. -/
theorem exists_disk_evaluation_constant (m : ℕ) (S : Finset ℂ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℂ[X]) (H : ℝ), P.natDegree ≤ m → 0 ≤ H →
      (∀ z : ℂ, ‖z‖ ≤ 2 → ‖P.eval z‖ ≤ H) → ∀ z ∈ S, ‖P.eval z‖ ≤ K * H := by
  classical
  let s := Finset.range (m + 1)
  let v (i : ℕ) : ℂ := (i : ℂ) / ((m + 1 : ℕ) : ℂ)
  have hden : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hv : Set.InjOn v (s : Set ℕ) := by
    intro i _ j _ hij
    exact Nat.cast_injective (R := ℂ) ((div_left_inj' hden).mp hij)
  have hvdisk (i : ℕ) (hi : i ∈ s) : ‖v i‖ ≤ 2 := by
    have hle : (i : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_range.mp hi).le
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    simp only [v, norm_div, Complex.norm_natCast]
    apply (div_le_one hpos).mpr hle |>.trans
    norm_num
  let B (z : ℂ) := ∑ i ∈ s, ‖(Lagrange.basis s v i).eval z‖
  have hB (z : ℂ) : 0 ≤ B z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ z ∈ S, B z, le_add_of_nonneg_right (Finset.sum_nonneg fun z _ => hB z), ?_⟩
  intro P H hp hH hbound z hz
  have hdeg : P.degree < (s.card : WithBot ℕ) := degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (by simpa [s] using Nat.lt_succ_of_le hp))
  have hrep := Lagrange.eq_interpolate (f := P) hv hdeg
  have heval := congrArg (fun Q : ℂ[X] => Q.eval z) hrep
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at heval
  rw [heval]
  calc
    _ ≤ ∑ i ∈ s, ‖P.eval (v i) * (Lagrange.basis s v i).eval z‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, H * ‖(Lagrange.basis s v i).eval z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound _ (hvdisk i hi)) (norm_nonneg _)
    _ = B z * H := by rw [← Finset.mul_sum, mul_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact (Finset.single_le_sum (f := B) (fun y _ => hB y) hz).trans (le_add_of_nonneg_left zero_le_one)

end PiPolynomialValues
