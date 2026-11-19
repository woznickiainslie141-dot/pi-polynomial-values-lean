module

public import OddPiPowers.PolynomialValues.Numerics.MeshBlock

/-! Consecutive certified pieces compose by checking their shared
logarithm state. The resulting finite lookup has a theorem at every index. -/

@[expose] public section

namespace PiPolynomialValues

structure MeshPiece where
  start : ℕ
  size : ℕ
  lo : ℕ
  hi : ℕ
  endLo : ℕ
  endHi : ℕ
  first : ℕ → ℤ
  second : ℕ → ℤ

def MeshPiece.Valid (p : MeshPiece) : Prop :=
  0<p.start → MeshLogState p.start p.lo p.hi →
    MeshLogState (p.start+p.size) p.endLo p.endHi ∧
      ∀ k<p.size, MeshPrimitiveEnclosed (p.start+k) (p.first k) (p.second k)

def MeshBlock.piece (b : MeshBlock) : MeshPiece :=
  ⟨b.start,b.size,b.firstLo,b.firstHi,b.lastLo,b.lastHi,meshFWord b.fData,meshJWord b.jData⟩

theorem MeshBlock.piece_valid (b : MeshBlock) (h : b.passes=true) : b.piece.Valid := b.sound h

def MeshPiece.append (p q : MeshPiece) : MeshPiece :=
  ⟨p.start,p.size+q.size,p.lo,p.hi,q.endLo,q.endHi,
   fun k => if k<p.size then p.first k else q.first (k-p.size),
   fun k => if k<p.size then p.second k else q.second (k-p.size)⟩

def MeshPiece.joins (p q : MeshPiece) : Bool :=
  decide (p.start+p.size=q.start ∧ p.endLo=q.lo ∧ p.endHi=q.hi)

theorem MeshPiece.append_valid {p q : MeshPiece} (hp : p.Valid) (hq : q.Valid)
    (hj : p.joins q=true) : (p.append q).Valid := by
  obtain ⟨hi,hl,hh⟩ := of_decide_eq_true hj
  intro h0 hs
  obtain ⟨hstate,h1⟩ := hp h0 hs
  rw [hi,hl,hh] at hstate
  obtain ⟨hend,h2⟩ := hq (by change 0<p.start at h0; omega) hstate
  refine ⟨?_,?_⟩
  · simpa only [append,← Nat.add_assoc,hi] using hend
  · intro k hk
    change k<p.size+q.size at hk
    by_cases h : k<p.size
    · simpa [append,h] using h1 k h
    · have he : q.start+(k-p.size)=p.start+k := by omega
      simpa [append,h,he] using h2 (k-p.size) (by omega)

def MeshPiece.lookupF (p : MeshPiece) (i : ℕ) : ℤ := if i=0 then 0 else p.first (i-1)
def MeshPiece.lookupJ (p : MeshPiece) (i : ℕ) : ℤ := if i=0 then 0 else p.second (i-1)

theorem MeshPiece.lookup_enclosed {p : MeshPiece} (hp : p.Valid) (hst : p.start=1)
    (hl : p.lo=0) (hh : p.hi=0) (i : ℕ) (hi : i≤p.size) :
    MeshPrimitiveEnclosed i (p.lookupF i) (p.lookupJ i) := by
  have hain : MeshLogState p.start p.lo p.hi := by rw [hst,hl,hh]; exact meshLogState_one
  have HB := (hp (by omega) hain).2
  cases i with
  | zero => norm_num [lookupF,lookupJ,MeshPrimitiveEnclosed,logPrimitive,energyPrimitive]
  | succ i =>
    have h := HB i (by omega)
    simpa [lookupF,lookupJ,hst,Nat.add_comm] using h

end PiPolynomialValues
