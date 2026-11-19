module

public import OddPiPowers.PolynomialValues.Numerics.CompactJumpWord
public import OddPiPowers.PolynomialValues.Numerics.CompactDilation

/-! Recover the original fine-grid residual components from the
certified compact total jump sequence in both orientations. -/

@[expose] public section

namespace PiPolynomialValues

def preparedCoefficients (word : ℕ) (ws : List ℕ) :=
  let edge := shiftedBand ws
  (2*(-1))*lagWord 80001 (edge-compactDilate (compactJump word))
    (-edge-compactDilate (fun j => compactJump word (640-j)))

theorem preparedCoefficients_eq (rows : List SpatialLane) (ws : List ℕ) (word : ℕ)
    (hp : (rows.map SpatialLane.packed).sum=wide641 word) :
    residualCoefficients rows ws=preparedCoefficients word ws := by
  dsimp only [residualCoefficients,preparedCoefficients]
  rw [dilateJumps_congr (f := summedJumpAt (summedJumpWord rows)) (g := compactJump word)
      (fun i hi => summedJump_compact rows word hp hi),
    dilateJumps_congr (f := fun j => summedJumpAt (summedJumpWord rows) (640-j))
      (g := fun j => compactJump word (640-j)) (fun i _ => summedJump_compact rows word hp (by omega))]

def preparedPrimitive (basis : EnergySection 80001 1 0 80001) (word : ℕ) (ws : List ℕ) :=
  packedDot energyBase energyBias 80001 (preparedCoefficients word ws) basis.word

def preparedRounding (word : ℕ) (ws : List ℕ) :=
  2*packedDot energyBase energyBias 80001 (packedPositive 191 80001 (preparedCoefficients word ws))
    (packedOnes energyBase 80001)

theorem primitiveComponent_prepared (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ)
    (word : ℕ) (hp : (rows.map SpatialLane.packed).sum=wide641 word) :
    primitiveComponent basis rows ws=preparedPrimitive basis word ws := by
  simp only [primitiveComponent,preparedPrimitive,preparedCoefficients_eq rows ws word hp]

theorem roundingComponent_prepared (rows : List SpatialLane) (ws : List ℕ) (word : ℕ)
    (hp : (rows.map SpatialLane.packed).sum=wide641 word) :
    roundingComponent rows ws=preparedRounding word ws := by
  simp only [roundingComponent,preparedRounding,preparedCoefficients_eq rows ws word hp]

end PiPolynomialValues
