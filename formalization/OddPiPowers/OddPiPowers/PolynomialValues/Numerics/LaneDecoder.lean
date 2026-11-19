module

public import OddPiPowers.PolynomialValues.Numerics.SpatialLane

/-! Read a packed density word one signed coefficient at a time. The same
recurrence checks the polynomial value, total mass and absolute variation. -/

@[expose] public section

namespace PiPolynomialValues

def laneMoment (b : ℤ) (f : ℤ → ℤ) : ℕ → ℕ → ℤ
  | 0,_ => 0
  | n+1,d => f (meshFWord d 0)+laneMoment b f n (d/2^32)*b

theorem laneMoment_eq (b : ℤ) (f : ℤ → ℤ) (n d : ℕ) :
    laneMoment b f n d=packEval b n (fun j => f (meshFWord d j)) := by
  rw [packEval_eq]
  induction n generalizing d with
  | zero => simp [laneMoment,packedSum]
  | succ n ih =>
    rw [laneMoment,packedSum_shift,ih]
    simp only [meshFWord,meshWord_succ]

def SpatialLane.decoded (v : SpatialLane) : Bool := decide
  (v.packed=laneMoment spatialBase id 641 v.data ∧ laneMoment 1 id 641 v.data=0 ∧
   v.norm=laneMoment 1 abs 641 v.data ∧ v.norm≤10^12 ∧ |v.slope|≤10^8 ∧ |v.β|≤10^8)

theorem SpatialLane.decoded_eq (v : SpatialLane) : v.decoded=v.passes := by
  simp only [decoded,passes,laneMoment_eq,Function.id_def,jump]
  rfl

theorem decoded_rows_sound (rows : List SpatialLane) (h : rows.all SpatialLane.decoded=true) :
    rows.all SpatialLane.passes=true := by
  rw [show SpatialLane.decoded=SpatialLane.passes from funext SpatialLane.decoded_eq] at h
  exact h

end PiPolynomialValues
