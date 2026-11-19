module

public import OddPiPowers.PolynomialValues.Numerics.PackedWindows

/-! A constant interval of mesh weights has a closed geometric word.
The same construction handles reversed weights for scalar products. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

theorem packedSum_congr {b : ℤ} {n : ℕ} {a c : ℕ → ℤ} (h : ∀ i<n, a i=c i) :
    packedSum b n a=packedSum b n c := by
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi)]

def spanWord (b : ℤ) (n l u : ℕ) := packedOnes b (min n u-min n l)*b^(min n l)

theorem spanWord_sound {b : ℤ} (hb : 1<b) (n l u : ℕ) :
    spanWord b n l u=packedSum b n (fun k => if l≤k ∧ k<u then 1 else 0) := by
  let a := min n l
  let c := min n u
  let f (k : ℕ) : ℤ := if l≤k ∧ k<u then 1 else 0
  by_cases ha : a≤c
  · have H : a+(c-a)+(n-c)=n := by dsimp [a,c] at *; omega
    have he : packedSum b n f = packedSum b a f+
        packedSum b (c-a) (fun j => f (a+j))*b^a+
        packedSum b (n-c) (fun j => f (a+(c-a)+j))*b^(a+(c-a)) := by
      rw [← H,packedSum_append b (a+(c-a)),packedSum_append b a]
      rw [H]
    have h₁ : packedSum b a f=0 := by
      apply (packedSum_congr (c := fun _ => 0) (fun i hi => if_neg (by dsimp [a] at hi; omega))).trans
      simp [packedSum]
    have h₂ : packedSum b (c-a) (fun j => f (a+j))=packedOnes b (c-a) := by
      rw [packedOnes_eq hb]
      apply packedSum_congr
      intro i hi
      dsimp [a,c] at ha hi ⊢
      exact if_pos (by omega)
    have h₃ : packedSum b (n-c) (fun j => f (a+(c-a)+j))=0 := by
      apply (packedSum_congr (c := fun _ => 0) (fun i hi => if_neg (by dsimp [a,c] at *; omega))).trans
      simp [packedSum]
    change spanWord b n l u=packedSum b n f
    rw [he,h₁,h₂,h₃,zero_mul,add_zero,zero_add]
    rfl
  · have h : c-a=0 := by omega
    change packedOnes b (c-a)*b^a=packedSum b n f
    rw [h,packedOnes_eq hb]
    simp only [packedSum,range_zero,sum_empty,zero_mul]
    apply Eq.symm
    apply sum_eq_zero
    intro i hi
    have hi' := mem_range.mp hi
    rw [show f i=0 from if_neg (by dsimp [a,c] at ha; omega),zero_mul]

structure GridSpan where
  lo : ℕ
  hi : ℕ
deriving DecidableEq

def GridSpan.hit (s : GridSpan) (i : ℕ) : ℤ := if s.lo≤i ∧ i<s.hi then 1 else 0
def stripeCut (r a : ℕ) := (a+124-r)/125

theorem stripeCut_lt (r a k : ℕ) : k<stripeCut r a ↔ r+125*k<a := by unfold stripeCut; omega

def GridSpan.word (s : GridSpan) (b : ℤ) (r n : ℕ) := spanWord b n (stripeCut r s.lo) (stripeCut r s.hi)
def GridSpan.reversedWord (s : GridSpan) (b : ℤ) (r n : ℕ) :=
  spanWord b n (n-stripeCut r s.hi) (n-stripeCut r s.lo)

theorem GridSpan.word_sound (s : GridSpan) {b : ℤ} (hb : 1<b) (r n : ℕ) :
    s.word b r n=packedSum b n (fun k => s.hit (r+125*k)) := by
  rw [word,spanWord_sound hb]
  apply packedSum_congr
  intro k _
  have hl := stripeCut_lt r s.lo k
  have hh := stripeCut_lt r s.hi k
  dsimp only [hit]
  split_ifs <;> omega

theorem GridSpan.reversedWord_sound (s : GridSpan) {b : ℤ} (hb : 1<b) (r n : ℕ) :
    s.reversedWord b r n=packEval b n (fun k => s.hit (r+125*(n-1-k))) := by
  rw [reversedWord,spanWord_sound hb,packEval_eq]
  apply packedSum_congr
  intro k hk
  have hl := stripeCut_lt r s.lo (n-1-k)
  have hh := stripeCut_lt r s.hi (n-1-k)
  dsimp only [hit]
  split_ifs <;> omega

end PiPolynomialValues
