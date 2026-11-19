module

public import OddPiPowers.PolynomialValues.Numerics.PackedComparison
public import Mathlib.Algebra.Order.Ring.Abs

/-! A product evaluates the convolution of two signed integer rows.
The absolute sum of the shorter row controls every coefficient,
including the two incomplete ends of the product. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Polynomial

def packLoop (b : ℤ) (a : ℕ → ℤ) : ℕ → ℤ → ℤ
  | 0, z => z
  | n+1, z => packLoop b a n (z*b+a n)

def packEval (b : ℤ) (n : ℕ) (a : ℕ → ℤ) := packLoop b a n 0

theorem packLoop_eq (b : ℤ) (a : ℕ → ℤ) (n : ℕ) (z : ℤ) :
    packLoop b a n z=z*b^n+packedSum b n a := by
  induction n generalizing z with
  | zero => simp [packLoop,packedSum]
  | succ n ih =>
    rw [packLoop,ih,packedSum,packedSum,sum_range_succ,pow_succ]
    ring

theorem packEval_eq (b : ℤ) (n : ℕ) (a : ℕ → ℤ) : packEval b n a=packedSum b n a := by
  simp [packEval,packLoop_eq]

theorem coefficientPoly_degree {m : ℕ} (hm : 0<m) (a : ℕ → ℤ) : (coefficientPoly m a).natDegree<m := by
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le (range m) _ (n := m-1) ?_) (by omega)
  intro i hi
  exact (natDegree_monomial_le _).trans (by have := mem_range.mp hi; omega)

def meshConvolution (m n : ℕ) (a c : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ range n, (if j≤k ∧ k-j<m then a (k-j) else 0)*c j

theorem meshConvolution_coeff (m n : ℕ) (a c : ℕ → ℤ) (k : ℕ) :
    ((coefficientPoly m a)*(coefficientPoly n c)).coeff k=meshConvolution m n a c k := by
  let P := coefficientPoly m a
  change (P*∑ j ∈ range n, monomial j (c j)).coeff k=_
  rw [mul_sum,finsetSum_coeff]
  apply sum_congr rfl
  intro j _
  rw [← C_mul_X_pow_eq_monomial,← mul_assoc,coeff_mul_X_pow',coeff_mul_C]
  simp only [P,coefficientPoly_coeff]
  split_ifs <;> simp_all

theorem meshConvolution_abs {m n : ℕ} {a c : ℕ → ℤ} {A : ℤ} (hA : 0≤A)
    (ha : ∀ i<m, |a i|≤A) (k : ℕ) :
    |meshConvolution m n a c k| ≤ A*(∑ j ∈ range n, |c j|) := by
  unfold meshConvolution
  rw [mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro j _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  split_ifs with h
  · exact ha _ h.2
  · simpa using hA

theorem meshConvolution_interior {m n k : ℕ} (hn : n≤k+1) (hm : k<m) (a c : ℕ → ℤ) :
    meshConvolution m n a c k=∑ j ∈ range n, a (k-j)*c j := by
  unfold meshConvolution
  apply sum_congr rfl
  intro j hj
  have h := mem_range.mp hj
  rw [if_pos (by constructor <;> omega)]

theorem packedProduct_eq {m n : ℕ} (hm : 0<m) (hn : 0<n) {b : ℤ} (a c : ℕ → ℤ) (bias : ℤ) :
    packEval b m a*packEval b n c+bias*packedSum b (m+n) (fun _ => 1) =
      packedSum b (m+n) (fun k => meshConvolution m n a c k+bias) := by
  let P := coefficientPoly m a
  let Q := coefficientPoly n c
  have hdeg : (P*Q).natDegree<m+n := by
    apply natDegree_mul_le.trans_lt
    have hp := coefficientPoly_degree hm a
    have hq := coefficientPoly_degree hn c
    dsimp [P,Q]
    omega
  rw [packEval_eq,packEval_eq,← coefficientPoly_eval,← coefficientPoly_eval,← eval_mul]
  change (P*Q).eval b+_=_
  rw [eval_eq_sum_range' hdeg]
  simp only [P,Q,meshConvolution_coeff,packedSum,add_mul,sum_add_distrib,mul_sum,one_mul]

end PiPolynomialValues
