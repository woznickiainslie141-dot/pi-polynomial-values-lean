module

public import OddPiPowers.PolynomialValues.Analysis.NormalizedBlockBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A one-sided elementary Barnes product estimate with explicit error,
sufficient for the determinant after cancellation of its scale powers. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real

private theorem nat_log_step (k : ℕ) :
    (k : ℝ)*(log ((k : ℝ)+1)-log (k : ℝ)) ≤ 1 := by
  by_cases h : k=0
  · simp [h]
  have hk : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
  rw [← log_div (by positivity) hk.ne']
  have hh := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (show 0 < ((k : ℝ)+1)/k by positivity)) hk.le
  apply hh.trans_eq
  field_simp
  ring

theorem log_factorial_lower (k : ℕ) : (k : ℝ)*log (k : ℝ)-k ≤ log (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ,Nat.cast_mul,log_mul (by positivity) (by positivity),Nat.cast_succ]
    nlinarith [nat_log_step k]

noncomputable def factorialPrimitive (x : ℝ) := x^2*log x/2-3*x^2/4

private theorem factorialPrimitive_step (k : ℕ) :
    factorialPrimitive ((k : ℝ)+1)-factorialPrimitive k ≤
      log (k.factorial : ℝ)+1+log ((k : ℝ)+1) := by
  have hin := nat_log_step k
  have hp : 0 ≤ log ((k : ℝ)+1) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])
  unfold factorialPrimitive
  nlinarith [mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg (α := ℝ) k),log_factorial_lower k]

theorem factorialPrefix_lower (m : ℕ) : factorialPrimitive m ≤
    (∑ k ∈ range m, log (k.factorial : ℝ)) + m*(1+log ((m : ℝ)+1)) := by
  induction m with
  | zero => simp [factorialPrimitive]
  | succ m ih =>
    have hg : log ((m : ℝ)+1) ≤ log ((m : ℝ)+1+1) := log_le_log (by positivity) (by linarith)
    rw [sum_range_succ,Nat.cast_succ]
    nlinarith [factorialPrimitive_step m,mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) m)]

theorem factorialWeight_pos (m : ℕ) : 0 < factorialWeight m :=
  prod_pos fun i _ => by positivity

theorem log_factorialWeight_upper (m : ℕ) :
    log (factorialWeight m) ≤ -factorialPrimitive m + m*(1+log ((m : ℝ)+1)) := by
  rw [factorialWeight,log_prod (fun _ _ => by positivity)]
  simp only [log_inv,sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun k => log (k.factorial : ℝ)) m]
  linarith [factorialPrefix_lower m]

end PiPolynomialValues.FourPeriod
