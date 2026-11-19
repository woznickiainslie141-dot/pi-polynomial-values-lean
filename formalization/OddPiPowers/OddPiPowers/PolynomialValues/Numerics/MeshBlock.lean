module

public import OddPiPowers.PolynomialValues.Numerics.MeshPrimitives

/-! A packed integer witness for a consecutive block of mesh values.
Every checked digit is transferred to both real primitive bounds. -/

@[expose] public section

namespace PiPolynomialValues

def meshTerms (i : ℕ) : ℕ :=
  if i<2 then 25 else if i<5 then 18 else if i<12 then 13 else if i<32 then 10
  else if i<128 then 7 else if i<1024 then 5 else if i<8000 then 4 else 3

def meshWord (base data k : ℕ) : ℕ := data/base^k % base

def meshFWord (data k : ℕ) : ℤ := (meshWord (2^32) data k : ℤ)-2^31
def meshJWord (data k : ℕ) : ℤ := (meshWord (2^48) data k : ℤ)-2^47

theorem meshWord_succ (b data k : ℕ) : meshWord b data (k+1)=meshWord b (data/b) k := by
  simp only [meshWord,pow_succ',Nat.div_div_eq_div_mul]

def meshRun (endLo endHi : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, lo, hi, f, j => decide (lo=endLo ∧ hi=endHi ∧ f=0 ∧ j=0)
  | k+1, i, lo, hi, f, j =>
    let n := meshTerms i
    let d := meshIncFloor i n
    decide (2*meshLogScale ≤ meshTermDen i n) &&
      (meshPrimitivePass i lo hi (meshFWord f 0) (meshJWord j 0) &&
        meshRun endLo endHi k (i+1) (lo+d) (hi+d+n+2) (f/(2^32)) (j/(2^48)))

theorem meshRun_sound {endLo endHi K i lo hi f j : ℕ} (hi' : 0 < i)
    (hs : MeshLogState i lo hi) (hc : meshRun endLo endHi K i lo hi f j=true) :
    MeshLogState (i+K) endLo endHi ∧
      ∀ k<K, MeshPrimitiveEnclosed (i+k) (meshFWord f k) (meshJWord j k) := by
  induction K generalizing i lo hi f j with
  | zero =>
    obtain ⟨rfl,rfl,_,_⟩ := of_decide_eq_true hc
    exact ⟨by simpa using hs,fun k hk => by omega⟩
  | succ K ih =>
    simp only [meshRun,Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨ht,hp,hr⟩ := hc
    obtain ⟨he,hrow⟩ := ih (Nat.succ_pos i) (hs.step hi' ht) hr
    refine ⟨by simpa only [Nat.add_succ,Nat.succ_add] using he,?_⟩
    intro k hk
    cases k with
    | zero => simpa only [Nat.add_zero] using meshPrimitive_sound hi' hs hp
    | succ k =>
      have h := hrow k (Nat.lt_of_succ_lt_succ hk)
      simpa only [meshFWord,meshJWord,meshWord_succ,Nat.add_succ,Nat.succ_add] using h

structure MeshBlock where
  start : ℕ
  size : ℕ
  firstLo : ℕ
  firstHi : ℕ
  lastLo : ℕ
  lastHi : ℕ
  fData : ℕ
  jData : ℕ

def MeshBlock.passes (b : MeshBlock) :=
  meshRun b.lastLo b.lastHi b.size b.start b.firstLo b.firstHi b.fData b.jData

theorem MeshBlock.sound (b : MeshBlock) (hb : b.passes=true) (hi : 0<b.start)
    (hs : MeshLogState b.start b.firstLo b.firstHi) :
    MeshLogState (b.start+b.size) b.lastLo b.lastHi ∧
      ∀ k<b.size, MeshPrimitiveEnclosed (b.start+k) (meshFWord b.fData k) (meshJWord b.jData k) :=
  meshRun_sound hi hs hb

end PiPolynomialValues
