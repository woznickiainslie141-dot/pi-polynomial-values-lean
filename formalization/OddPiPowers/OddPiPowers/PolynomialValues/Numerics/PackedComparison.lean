module

public import OddPiPowers.PolynomialValues.Numerics.PackedCoefficients
public import Mathlib.Data.Nat.Bits

/-! A single integer mask checks the sign of every coefficient of a
bounded packed difference. This gives pointwise upper bounds even when
the node attaining the envelope changes between mesh positions. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def packedOnes (b : ℤ) (n : ℕ) := (b^n-1)/(b-1)

theorem packedOnes_eq {b : ℤ} (hb : 1<b) (n : ℕ) :
    packedOnes b n=packedSum b n (fun _ => 1) := by
  have hn : b-1≠0 := by omega
  have he (k : ℕ) : (∑ i ∈ range k, b^i)*(b-1)=b^k-1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,add_mul,ih,pow_succ]; ring
  unfold packedOnes packedSum
  simp only [one_mul]
  rw [← he n,Int.mul_ediv_cancel _ hn]

def highMask (w n : ℕ) : ℕ := ((2 : ℤ)^w*packedOnes ((2 : ℤ)^(w+1)) n).toNat

def packedNonnegative (w n : ℕ) (z : ℤ) : Bool :=
  ((z.toNat &&& highMask w n) == highMask w n)

theorem packedSum_nonneg {b : ℤ} (hb : 0≤b) (n : ℕ) (a : ℕ → ℤ) (ha : ∀ k<n, 0≤a k) :
    0≤packedSum b n a := sum_nonneg (fun i hi => mul_nonneg (ha i (mem_range.mp hi)) (pow_nonneg hb _))

theorem toNat_packedDigit (w k : ℕ) {z : ℤ} (hz : 0≤z) :
    (↑(z.toNat/2^(w*k)%2^w) : ℤ)=packedDigit ((2 : ℤ)^w) z k := by
  simp [packedDigit,Int.toNat_of_nonneg hz,pow_mul]

theorem packed_word_bit (w k i z : ℕ) (hi : i<w) :
    (z/2^(w*k)%2^w).testBit i=z.testBit (i+w*k) := by
  simp [Nat.testBit_mod_two_pow,hi,Nat.testBit_div_two_pow]

theorem highMask_bit (w n k : ℕ) (hk : k<n) : (highMask w n).testBit (w+(w+1)*k)=true := by
  let b := (2 : ℤ)^(w+1)
  let a := (2 : ℤ)^w
  have ha : 0<a := by dsimp [a]; positivity
  have hb : b=2*a := by simp [b,a,pow_succ',mul_comm]
  have hgt : 1<b := by rw [hb]; omega
  have he : a*packedOnes b n=packedSum b n (fun _ => a) := by
    simp [packedOnes_eq hgt,packedSum,mul_sum]
  have hn := packedSum_nonneg (b := b) (by omega) n (fun _ => a) (fun _ _ => ha.le)
  have hv := packedDigit_eq (b := b) (by omega) (fun _ => a) (fun _ _ => ⟨ha.le,by omega⟩) hk
  have heq : highMask w n=(packedSum b n (fun _ => a)).toNat := congrArg Int.toNat he
  rw [heq,← packed_word_bit (w+1) k w _ (Nat.lt_succ_self _)]
  have hd : (packedSum b n (fun _ => a)).toNat/2^((w+1)*k)%2^(w+1)=2^w := by
    have H := (toNat_packedDigit (w+1) k hn).trans hv
    dsimp only [a] at H ⊢
    exact_mod_cast H
  rw [hd,Nat.testBit_two_pow_self]

theorem packedNonnegative_sound {w n : ℕ} (d : ℕ → ℤ)
    (hd : ∀ k<n, 0≤d k+2^w ∧ d k+2^w<(2 : ℤ)^(w+1))
    {z : ℤ} (he : z=packedSum ((2 : ℤ)^(w+1)) n (fun k => d k+2^w))
    (hc : packedNonnegative w n z=true) {k : ℕ} (hk : k<n) : 0≤d k := by
  have hz : 0≤z := he.symm ▸ packedSum_nonneg (by positivity) n _ (fun i hi => (hd i hi).1)
  have hmask : z.toNat &&& highMask w n=highMask w n := beq_iff_eq.mp hc
  have hm := congrArg (fun x : ℕ => x.testBit (w+(w+1)*k)) hmask
  simp only [Nat.testBit_and,highMask_bit w n k hk,Bool.and_true] at hm
  rw [← packed_word_bit (w+1) k w z.toNat (Nat.lt_succ_self _)] at hm
  have hl := Nat.ge_two_pow_of_testBit hm
  have hdigit : (↑(z.toNat/2^((w+1)*k)%2^(w+1)) : ℤ)=d k+2^w := by
    rw [toNat_packedDigit _ _ hz,he,packedDigit_eq (by positivity) _ hd hk]
  have hr : (2 : ℤ)^w≤↑(z.toNat/2^((w+1)*k)%2^(w+1)) := by exact_mod_cast hl
  omega

end PiPolynomialValues
