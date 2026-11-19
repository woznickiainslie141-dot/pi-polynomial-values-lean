module

public import OddPiPowers.PolynomialValues.Numerics.SummedResidual

/-! Dilate the 641 packed signed jumps to the fine grid using balanced
binary shifts. Each block only reads its own digits. The band endpoints
are constructed with a single shift of their integer height. -/

@[expose] public section

namespace PiPolynomialValues

def signedShift (a : ℤ) (k : ℕ) : ℤ := ((a.toNat <<< k : ℕ) : ℤ)-(((-a).toNat <<< k : ℕ) : ℤ)

theorem signedShift_eq (a : ℤ) (k : ℕ) : signedShift a k=a*(2:ℤ)^k := by
  simp only [signedShift,Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← sub_mul]
  rw [show (a.toNat : ℤ)-((-a).toNat : ℤ)=a by omega]

def strand (step : ℕ) (a : ℕ → ℤ) (s : ℕ) : ℕ → ℤ
  | 0 => a s
  | d+1 =>
    let m := 2^d
    strand step a s d+signedShift (strand step a (s+m) d) (step*m)

theorem strand_eq (step : ℕ) (a : ℕ → ℤ) (s d : ℕ) :
    strand step a s d=packedSum ((2:ℤ)^step) (2^d) (fun j => a (s+j)) := by
  induction d generalizing s with
  | zero => simp [strand,packedSum]
  | succ d ih =>
    rw [strand,signedShift_eq,ih,ih,show 2^(d+1)=2^d+2^d by rw [pow_succ]; omega,packedSum_append]
    simp only [← pow_mul,Nat.add_assoc]

def dilateJumps (a : ℕ → ℤ) :=
  strand 24000 a 0 9+
    signedShift (strand 24000 a 512 7+signedShift (a 640) (24000*128)) (24000*512)

theorem dilateJumps_eq (a : ℕ → ℤ) :
    dilateJumps a=coarseWord (energyBase^125) a := by
  have hb : energyBase^125=(2:ℤ)^24000 := by rw [energyBase,← pow_mul]
  rw [coarseWord_eq,hb,show 641=512+(128+1) by decide,
    packedSum_append ((2:ℤ)^24000) 512 129,packedSum_append ((2:ℤ)^24000) 128 1]
  have h₁ : packedSum ((2:ℤ)^24000) 1 (fun j => a (512+(128+j)))=a 640 := by simp [packedSum]
  simp only [dilateJumps,strand_eq,signedShift_eq,← pow_mul,h₁,Nat.zero_add] <;> rfl

def shiftedBand (widths : List ℕ) :=
  (widths.map fun w => signedShift 100000 (192*(40000-4*w))-signedShift 100000 (192*(40000+4*w))).sum

theorem shiftedBand_eq (widths : List ℕ) : shiftedBand widths=bandJumpWord energyBase widths := by
  unfold shiftedBand bandJumpWord
  apply congrArg List.sum
  apply List.map_congr_left
  intro w _
  rw [signedShift_eq,signedShift_eq,energyBase,← pow_mul,← pow_mul]
  ring

def shiftedResidual (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ) :=
  let w := summedJumpWord rows
  let edge := shiftedBand ws
  let a := summedJumpAt w
  lagEnergyWord 80001 (edge-dilateJumps a) (-edge-dilateJumps (fun j => a (640-j))) basis.word (-1)

theorem residualEnergy_shifted (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ)
    (checked : rows.all SpatialLane.passes=true) (budget : jumpBudget rows≤10^13) :
    residualEnergy basis rows ws=shiftedResidual basis rows ws := by
  rw [residualEnergy_summed _ _ _ checked budget]
  simp only [summedResidual,shiftedResidual,shiftedBand_eq,dilateJumps_eq]

def residualCoefficients (rows : List SpatialLane) (ws : List ℕ) :=
  let a := summedJumpAt (summedJumpWord rows)
  let edge := shiftedBand ws
  (2*(-1))*lagWord 80001 (edge-dilateJumps a) (-edge-dilateJumps (fun j => a (640-j)))

def primitiveComponent (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ) :=
  packedDot energyBase energyBias 80001 (residualCoefficients rows ws) basis.word

def roundingComponent (rows : List SpatialLane) (ws : List ℕ) :=
  2*packedDot energyBase energyBias 80001 (packedPositive 191 80001 (residualCoefficients rows ws)) (packedOnes energyBase 80001)

theorem residualEnergy_components (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ)
    (checked : rows.all SpatialLane.passes=true) (budget : jumpBudget rows≤10^13) :
    residualEnergy basis rows ws=primitiveComponent basis rows ws+roundingComponent rows ws := by
  rw [residualEnergy_shifted _ _ _ checked budget]
  rfl

end PiPolynomialValues
