module

public import OddPiPowers.PolynomialValues.Numerics.ShiftedResidual

/-! Dilate a signed jump sequence using a single case split on each integer. -/

@[expose] public section

namespace PiPolynomialValues

def moveSigned : ℤ → ℕ → ℤ
  | .ofNat a,k => ((a <<< k : ℕ) : ℤ)
  | .negSucc a,k => -(((a+1) <<< k : ℕ) : ℤ)

theorem moveSigned_eq (a : ℤ) (k : ℕ) : moveSigned a k=signedShift a k := by
  rw [signedShift_eq]
  cases a <;> simp [moveSigned,Nat.shiftLeft_eq,Int.negSucc_eq] <;> ring

def compactStrand (f : ℕ → ℤ) (s : ℕ) : ℕ → ℤ
  | 0 => f s
  | d+1 => compactStrand f s d+moveSigned (compactStrand f (s+2^d) d) (24000*2^d)

theorem compactStrand_eq (f : ℕ → ℤ) (s d : ℕ) : compactStrand f s d=strand 24000 f s d := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => simp only [compactStrand,strand,moveSigned_eq,ih]

def compactDilate (f : ℕ → ℤ) := compactStrand f 0 9+
  moveSigned (compactStrand f 512 7+moveSigned (f 640) (24000*128)) (24000*512)

theorem compactDilate_eq (f : ℕ → ℤ) : compactDilate f=dilateJumps f := by
  simp only [compactDilate,dilateJumps,moveSigned_eq,compactStrand_eq]

theorem dilateJumps_congr {f g : ℕ → ℤ} (h : ∀ i<641, f i=g i) : dilateJumps f=compactDilate g := by
  rw [compactDilate_eq,dilateJumps_eq,dilateJumps_eq,coarseWord_eq,coarseWord_eq]
  exact packedSum_congr h

end PiPolynomialValues
