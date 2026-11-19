module

public import OddPiPowers.PolynomialValues.Numerics.PreparedResidual

/-! Binary slices at the two accuracy scales used in the primitive energy. -/

@[expose] public section

namespace PiPolynomialValues

def energySlice (z : ℤ) (start size : ℕ) : ℤ :=
  match z with
  | .ofNat a => (((a >>> (192*start)) &&& (2^(192*size)-1) : ℕ) : ℤ)
  | .negSucc a => packedWindow energyBase (.negSucc a) start size

theorem energySlice_eq (z : ℤ) (start size : ℕ) :
    energySlice z start size=packedWindow energyBase z start size := by
  cases z with
  | ofNat a =>
    change (((a >>> (192*start)) &&& (2^(192*size)-1) : ℕ) : ℤ)=
      (a : ℤ)/((2:ℤ)^192)^start%((2:ℤ)^192)^size
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,Int.natCast_mod,Int.natCast_ediv]
    simp only [Nat.cast_pow,Nat.cast_ofNat,pow_mul]
  | negSucc a => rfl

def bitLag (n : ℕ) (x rev : ℤ) :=
  energySlice (x*rev+energyBias*packedOnes energyBase (n+n)) n n-
    energyBias*packedOnes energyBase n

def bitPrimitive (basis : EnergySection 80001 1 0 80001) (word : ℕ) (ws : List ℕ) :=
  let edge := shiftedBand ws
  let c := (2*(-1))*bitLag 80001 (edge-compactDilate (compactJump word))
    (-edge-compactDilate (fun j => compactJump word (640-j)))
  energySlice (c*basis.word+energyBias*packedOnes energyBase (80001+80001)) (80001-1) 1-energyBias

theorem preparedPrimitive_bit (basis : EnergySection 80001 1 0 80001) (word : ℕ) (ws : List ℕ) :
    preparedPrimitive basis word ws=bitPrimitive basis word ws := by
  simp only [preparedPrimitive,preparedCoefficients,bitPrimitive,bitLag,energySlice_eq,
    packedDot,lagWord,packedDigit,packedWindow,pow_one]

end PiPolynomialValues
