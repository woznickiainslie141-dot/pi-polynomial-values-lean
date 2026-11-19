module

public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.WideLane

/-! Check the sum of the coarse jump rows in one signed 32-bit encoding. -/

@[expose] public section

namespace PiPolynomialValues

def compactJump (word i : ℕ) : ℤ :=
  (((word >>> (32*i)) &&& (2^32-1) : ℕ) : ℤ)-2^31

theorem compactJump_eq (word i : ℕ) : compactJump word i=meshFWord word i := by
  simp only [compactJump,meshFWord,meshWord,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,pow_mul]

theorem compactJump_bounds (word i : ℕ) : -(2:ℤ)^31≤compactJump word i ∧ compactJump word i<(2:ℤ)^31 := by
  rw [compactJump_eq]
  have h : (meshWord (2^32) word i : ℤ)<2^32 := by
    exact_mod_cast Nat.mod_lt (word/(2^32)^i) (by decide : 0<2^32)
  change -(2:ℤ)^31≤(meshWord (2^32) word i : ℤ)-2^31 ∧ (meshWord (2^32) word i : ℤ)-2^31<(2:ℤ)^31
  omega

theorem summedJump_compact (rows : List SpatialLane) (word : ℕ)
    (hp : (rows.map SpatialLane.packed).sum=wide641 word) {i : ℕ} (hi : i<641) :
    summedJumpAt (summedJumpWord rows) i=compactJump word i := by
  have he : summedJumpWord rows=packedSum spatialBase 641 (fun j => compactJump word j+2^63) := by
    have hf : compactJump word=meshFWord word := funext (compactJump_eq word)
    rw [summedJumpWord,hp,wide641_eq,packEval_eq,packedSum_add,packedSum_const (by decide : 1<spatialBase)]
    rw [hf]
  rw [summedJumpAt,he,packedDigit_eq (by decide : 0<spatialBase) _ (fun k _ => ?_) hi]
  · omega
  · have h := compactJump_bounds word k
    change 0≤compactJump word k+2^63 ∧ compactJump word k+2^63<(2:ℤ)^128
    omega

end PiPolynomialValues
