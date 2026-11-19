module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

/-! A coefficient certificate using ordinary integer multiplication.
A signed convolution is recovered exactly from its biased base digits
when every coefficient lies in the proved word range. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Polynomial

def packedSum (b : ℤ) (n : ℕ) (a : ℕ → ℤ) := ∑ i ∈ range n, a i*b^i
def packedDigit (b : ℤ) (z : ℤ) (k : ℕ) := z/b^k%b

theorem packedSum_shift (b : ℤ) (n : ℕ) (a : ℕ → ℤ) :
    packedSum b (n+1) a=a 0+packedSum b n (fun i => a (i+1))*b := by
  rw [packedSum,sum_range_succ',packedSum,sum_mul]
  simp only [pow_zero,mul_one,pow_succ,mul_assoc,add_comm]

theorem packedDigit_eq {b : ℤ} (hb : 0<b) {n : ℕ} (a : ℕ → ℤ) (ha : ∀ i<n, 0≤a i ∧ a i<b)
    {k : ℕ} (hk : k<n) : packedDigit b (packedSum b n a) k=a k := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    rw [packedSum_shift]
    have h0 := ha 0 (Nat.succ_pos n)
    cases k with
    | zero => simp [packedDigit,Int.add_mul_emod_self_right,Int.emod_eq_of_lt h0.1 h0.2]
    | succ k =>
      have hs := ih (fun i => a (i+1)) (fun j hj => ha (j+1) (Nat.succ_lt_succ hj)) (Nat.lt_of_succ_lt_succ hk)
      unfold packedDigit at hs ⊢
      rw [pow_succ',← Int.ediv_ediv_of_nonneg hb.le,Int.add_mul_ediv_right _ _ hb.ne',
        Int.ediv_eq_zero_of_lt h0.1 h0.2,zero_add]
      exact hs

noncomputable def coefficientPoly (n : ℕ) (a : ℕ → ℤ) : ℤ[X] := ∑ i ∈ range n, monomial i (a i)

theorem coefficientPoly_eval (n : ℕ) (a : ℕ → ℤ) (b : ℤ) :
    (coefficientPoly n a).eval b=packedSum b n a := by
  simp [coefficientPoly,packedSum,eval_finsetSum]

theorem coefficientPoly_coeff (n : ℕ) (a : ℕ → ℤ) (k : ℕ) :
    (coefficientPoly n a).coeff k=if k<n then a k else 0 := by
  classical
  simp only [coefficientPoly,finsetSum_coeff,coeff_monomial]
  simp [eq_comm]

theorem eval_biased_digit (P : ℤ[X]) {b : ℤ} (hb : 0<b) (n : ℕ) (hdeg : P.natDegree<n)
    (bias : ℤ) (ha : ∀ i<n, 0≤P.coeff i+bias ∧ P.coeff i+bias<b) {k : ℕ} (hk : k<n) :
    packedDigit b (P.eval b + bias*packedSum b n (fun _ => 1)) k-bias=P.coeff k := by
  have he : P.eval b+bias*packedSum b n (fun _ => 1)=packedSum b n (fun i => P.coeff i+bias) := by
    rw [eval_eq_sum_range' hdeg]
    simp [packedSum,add_mul,sum_add_distrib,mul_sum]
  rw [he,packedDigit_eq hb _ ha hk]
  omega

theorem convolution_digit (p q : ℤ[X]) {b : ℤ} (hb : 0<b) (n : ℕ) (hd : p.natDegree+q.natDegree<n)
    (bias : ℤ) (ha : ∀ i<n, 0≤(p*q).coeff i+bias ∧ (p*q).coeff i+bias<b)
    {k : ℕ} (hk : k<n) :
    packedDigit b (p.eval b*q.eval b+bias*packedSum b n (fun _ => 1)) k-bias=(p*q).coeff k := by
  rw [← eval_mul]
  exact eval_biased_digit _ hb n (natDegree_mul_le.trans_lt hd) bias ha hk

end PiPolynomialValues
