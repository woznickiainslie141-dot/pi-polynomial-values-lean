module

public import OddPiPowers.PolynomialValues.Numerics.PackedConvolution

/-! Slicing a packed product recovers a whole contiguous block of
convolution coefficients. Integer additions combine signed blocks
without requiring the separate summands to have unsigned coefficients. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

theorem packedSum_add (b : ℤ) (n : ℕ) (a c : ℕ → ℤ) :
    packedSum b n (fun i => a i+c i)=packedSum b n a+packedSum b n c := by
  simp [packedSum,add_mul,sum_add_distrib]

theorem packedSum_sub (b : ℤ) (n : ℕ) (a c : ℕ → ℤ) :
    packedSum b n (fun i => a i-c i)=packedSum b n a-packedSum b n c := by
  simp [packedSum,sub_mul,sum_sub_distrib]

theorem packedSum_scale (b : ℤ) (n : ℕ) (t : ℤ) (a : ℕ → ℤ) :
    packedSum b n (fun i => t*a i)=t*packedSum b n a := by
  simp [packedSum,mul_sum,mul_assoc]

theorem packedSum_const {b : ℤ} (hb : 1<b) (n : ℕ) (c : ℤ) :
    packedSum b n (fun _ => c)=c*packedOnes b n := by
  simp [packedOnes_eq hb,packedSum,mul_sum]

theorem packedSum_append (b : ℤ) (s n : ℕ) (a : ℕ → ℤ) :
    packedSum b (s+n) a=packedSum b s a+packedSum b n (fun j => a (s+j))*b^s := by
  simp only [packedSum,sum_range_add,sum_mul,pow_add]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

theorem packedSum_lt_pow {b : ℤ} (hb : 0<b) (n : ℕ) (a : ℕ → ℤ) (ha : ∀ k<n, a k<b) :
    packedSum b n a<b^n := by
  induction n with
  | zero => simp [packedSum]
  | succ n ih =>
    have H := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
    have hc : a n ≤ b-1 := by have := ha n (Nat.lt_succ_self n); omega
    have hz := mul_le_mul_of_nonneg_right hc (pow_nonneg hb.le n)
    rw [packedSum,sum_range_succ,← packedSum,pow_succ]
    linarith

def packedWindow (b z : ℤ) (s n : ℕ) := (z/b^s)%b^n

theorem packedWindow_eq {b : ℤ} (hb : 0<b) (s n t : ℕ) (a : ℕ → ℤ)
    (ha : ∀ i<s+n+t, 0≤a i ∧ a i<b) :
    packedWindow b (packedSum b (s+n+t) a) s n=packedSum b n (fun j => a (s+j)) := by
  let A := packedSum b s a
  let B := packedSum b n (fun j => a (s+j))
  let C := packedSum b t (fun j => a (s+n+j))
  have hA : 0≤A := packedSum_nonneg hb.le _ _ (fun i hi => (ha i (by omega)).1)
  have hA' : A<b^s := packedSum_lt_pow hb _ _ (fun i hi => (ha i (by omega)).2)
  have hB : 0≤B := packedSum_nonneg hb.le _ _ (fun i hi => (ha (s+i) (by omega)).1)
  have hB' : B<b^n := packedSum_lt_pow hb _ _ (fun i hi => (ha (s+i) (by omega)).2)
  have he : packedSum b (s+n+t) a=A+(B+C*b^n)*b^s := by
    rw [packedSum_append b (s+n) t,packedSum_append b s n,pow_add]
    change A+B*b^s+C*(b^s*b^n)=_
    ring
  rw [packedWindow,he,Int.add_mul_ediv_right _ _ (pow_ne_zero _ hb.ne'),Int.ediv_eq_zero_of_lt hA hA',
    zero_add,Int.add_mul_emod_self_right,Int.emod_eq_of_lt hB hB']

theorem packed_product_window {m n : ℕ} (hm : 0<m) (hn : 0<n) {b : ℤ} (hb : 1<b)
    (a c : ℕ → ℤ) (bias : ℤ) (s len : ℕ) (hs : s+len≤m+n)
    (hr : ∀ k<m+n, 0≤meshConvolution m n a c k+bias ∧ meshConvolution m n a c k+bias<b) :
    packedWindow b (packEval b m a*packEval b n c+bias*packedOnes b (m+n)) s len-
      bias*packedOnes b len=packedSum b len (fun k => meshConvolution m n a c (s+k)) := by
  have he : s+len+(m+n-(s+len))=m+n := by omega
  rw [packedOnes_eq hb,packedProduct_eq hm hn]
  nth_rw 1 [← he]
  rw [packedWindow_eq (by omega) s len _ _ (fun k hk => hr k (by omega)),
    packedSum_add,packedSum_const hb]
  ring

end PiPolynomialValues
