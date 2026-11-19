module

public import OddPiPowers.PolynomialValues.Numerics.PackedWindows

/-! Bitwise intersection of packed nonnegative words acts on each
word separately. This permits pointwise maxima without storing samples
of the upper envelope. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def natWordSum (p n : ℕ) (a : ℕ → ℕ) := ∑ i ∈ range n, a i*(2^p)^i

theorem natWordSum_cast (p n : ℕ) (a : ℕ → ℕ) :
    (natWordSum p n a : ℤ)=packedSum ((2 : ℤ)^p) n (fun i => (a i : ℤ)) := by
  simp [packedSum,natWordSum]

theorem natWordSum_step (p n : ℕ) (a : ℕ → ℕ) :
    natWordSum p (n+1) a=a 0+natWordSum p n (fun i => a (i+1))*2^p := by
  apply Int.ofNat_inj.mp
  push_cast
  simpa only [natWordSum_cast] using packedSum_shift ((2 : ℤ)^p) n (fun i => (a i : ℤ))

theorem natWordSum_and (p n : ℕ) (a c : ℕ → ℕ) (ha : ∀ i<n, a i<2^p) (hc : ∀ i<n, c i<2^p) :
    natWordSum p n a &&& natWordSum p n c=natWordSum p n (fun i => a i &&& c i) := by
  induction n generalizing a c with
  | zero => simp [natWordSum]
  | succ n ih =>
    have h := ih (fun i => a (i+1)) (fun i => c (i+1)) (fun i hi => ha _ (Nat.succ_lt_succ hi))
      (fun i hi => hc _ (Nat.succ_lt_succ hi))
    have h₁ := ha 0 (Nat.succ_pos n)
    have h₂ := hc 0 (Nat.succ_pos n)
    have ht : 0<2^p := by positivity
    rw [natWordSum_step,natWordSum_step,natWordSum_step]
    rw [← Nat.mod_add_div' ((_ + _*2^p) &&& (_ + _*2^p)) (2^p)]
    rw [Nat.and_mod_two_pow,Nat.and_div_two_pow]
    simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt h₁,Nat.mod_eq_of_lt h₂,
      Nat.add_mul_div_right _ _ ht,Nat.div_eq_of_lt h₁,Nat.div_eq_of_lt h₂,zero_add,h]

theorem natWordSum_scale (p n t : ℕ) (a : ℕ → ℕ) :
    natWordSum p n (fun i => t*a i)=t*natWordSum p n a := by
  simp [natWordSum,mul_sum,mul_assoc]

theorem natWordSum_congr {p n : ℕ} {a c : ℕ → ℕ} (h : ∀ i<n, a i=c i) : natWordSum p n a=natWordSum p n c := by
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi)]

theorem word_and_top (w z : ℕ) (hz : z<2^(w+1)) : z &&& 2^w=if 2^w≤z then 2^w else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : w=i
  · subst i
    by_cases h : 2^w≤z
    · simp [h,Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h hz,Nat.testBit_two_pow_self]
    · simp [h,Nat.testBit_lt_two_pow (lt_of_not_ge h),Nat.testBit_two_pow_self]
  · rw [Nat.testBit_two_pow_of_ne hi]
    split_ifs <;> simp [Nat.testBit_two_pow_of_ne hi]

def packedPositive (w n : ℕ) (d : ℤ) : ℤ :=
  let h := 2^w
  let m := highMask w n
  let x := (d+(m : ℤ)).toNat
  let flags := (x &&& m)/h
  ((x &&& ((h-1)*flags) : ℕ) : ℤ)

theorem highMask_words (w n : ℕ) :
    highMask w n=natWordSum (w+1) n (fun _ => 2^w) := by
  have hgt : 1<(2 : ℤ)^(w+1) := by rw [pow_succ]; have := pow_pos (by decide : (0 : ℤ)<2) w; omega
  have he : (2 : ℤ)^w*packedOnes ((2 : ℤ)^(w+1)) n=(natWordSum (w+1) n (fun _ => 2^w) : ℤ) := by
    rw [natWordSum_cast]
    simpa using (packedSum_const hgt n ((2 : ℤ)^w)).symm
  exact congrArg Int.toNat he

theorem packedPositive_sound (w n : ℕ) (d : ℕ → ℤ)
    (hd : ∀ i<n, -(2 : ℤ)^w≤d i ∧ d i<(2 : ℤ)^w) :
    packedPositive w n (packedSum ((2 : ℤ)^(w+1)) n d)=
      packedSum ((2 : ℤ)^(w+1)) n (fun i => max 0 (d i)) := by
  let h : ℕ := 2^w
  let a (i : ℕ) := (d i+(h : ℤ)).toNat
  let flag (i : ℕ) := if h≤a i then 1 else 0
  have hh : 0<h := pow_pos (by decide) _
  have he : 2^(w+1)=h+h := by dsimp [h]; rw [pow_succ]; omega
  have hcast : (h : ℤ)=(2 : ℤ)^w := by simp [h]
  have hv (i : ℕ) (hi : i<n) : (a i : ℤ)=d i+h := by
    have H := (hd i hi).1
    dsimp only [a]
    rw [Int.toNat_of_nonneg (by rw [hcast]; omega)]
  have ha (i : ℕ) (hi : i<n) : a i<2^(w+1) := by
    have H := (hd i hi).2
    rw [he]
    have D := hv i hi
    omega
  have hc : (highMask w n : ℤ)=packedSum ((2 : ℤ)^(w+1)) n (fun _ => (h : ℤ)) := by
    rw [highMask_words,natWordSum_cast]
  have hx : (packedSum ((2 : ℤ)^(w+1)) n d+(highMask w n : ℤ)).toNat=natWordSum (w+1) n a := by
    have e : packedSum ((2 : ℤ)^(w+1)) n d+(highMask w n : ℤ)=(natWordSum (w+1) n a : ℤ) := by
      rw [hc,← packedSum_add,natWordSum_cast]
      apply sum_congr rfl
      intro i hi
      dsimp only
      rw [hv i (mem_range.mp hi)]
    exact congrArg Int.toNat e
  have hxmask : natWordSum (w+1) n a &&& highMask w n = h*natWordSum (w+1) n flag := by
    rw [highMask_words,natWordSum_and _ _ _ _ ha (fun _ _ => by rw [he]; omega),← natWordSum_scale]
    apply natWordSum_congr
    intro i hi
    rw [word_and_top _ _ (ha i hi)]
    change (if h≤a i then h else 0)=h*flag i
    by_cases h₀ : h≤a i <;> simp [flag,h₀]
  have hm (i : ℕ) (hi : i<n) : (h-1)*flag i<2^(w+1) := by
    rw [he]
    by_cases hz : h≤a i <;> simp [flag,hz] <;> omega
  dsimp only [packedPositive]
  rw [hx,hxmask,show h*natWordSum (w+1) n flag/2^w=natWordSum (w+1) n flag from
    Nat.mul_div_cancel_left _ hh,← natWordSum_scale,natWordSum_and _ _ _ _ ha hm,natWordSum_cast]
  apply sum_congr rfl
  intro i hi
  congr 1
  have H := hv i (mem_range.mp hi)
  have H' := ha i (mem_range.mp hi)
  rw [he] at H'
  by_cases hz : h≤a i
  · have hpos : 0≤d i := by omega
    simp only [flag,if_pos hz,mul_one,max_eq_right hpos]
    rw [show h-1=2^w-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
    have her : a i%h=a i-h := by rw [Nat.mod_eq_sub_mod hz,Nat.mod_eq_of_lt (by omega)]
    rw [show a i%2^w=a i-h from her,Nat.cast_sub hz]
    omega
  · have hneg : d i≤0 := by omega
    simp [flag,hz,max_eq_left hneg]

end PiPolynomialValues
