module

public import OddPiPowers.PolynomialValues.Numerics.LagEnergyWord
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.All

/-! Sections can be checked independently and joined without reducing the
global primitive lookup again. Both the fine and coarse energy grid use
the same certified second primitive. -/

@[expose] public section

namespace PiPolynomialValues

open Certificates

def lagPrimitive (n step k : ℕ) : ℤ :=
  if k+1<n then primitiveMesh.lookupJ ((k+1)*step) else 0

def reverseLagPrimitive (n step j : ℕ) : ℤ := lagPrimitive n step (n-1-j)

structure WordSection (b : ℤ) (f : ℕ → ℤ) (start size : ℕ) where
  word : ℤ
  checked : word=packEval b size (fun j => f (start+j))

def WordSection.join {b : ℤ} {f : ℕ → ℤ} {s m n : ℕ}
    (p : WordSection b f s m) (q : WordSection b f (s+m) n) : WordSection b f s (m+n) where
  word := p.word+q.word*b^m
  checked := by
    rw [p.checked,q.checked,packEval_eq,packEval_eq,packEval_eq,packedSum_append b m n]
    simp only [Nat.add_assoc]

theorem WordSection.complete {b : ℤ} {f : ℕ → ℤ} {n : ℕ} (p : WordSection b f 0 n) :
    p.word=packEval b n f := by simpa using p.checked

abbrev EnergySection (n step start length : ℕ) := WordSection energyBase (reverseLagPrimitive n step) start length

end PiPolynomialValues
