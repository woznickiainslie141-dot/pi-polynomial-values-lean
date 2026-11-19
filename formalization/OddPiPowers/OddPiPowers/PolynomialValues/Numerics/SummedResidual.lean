module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy

/-! Sum the already validated signed jump words before changing the grid.
A fixed positive digit bias makes every coefficient recoverable without
re-decoding every constituent row at all 641 positions. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def summedJumpWord (rows : List SpatialLane) :=
  (rows.map SpatialLane.packed).sum+2^63*packedOnes spatialBase 641

def summedJumpAt (word : ℤ) (i : ℕ) := packedDigit spatialBase word i-2^63

theorem summedJumpWord_eq (rows : List SpatialLane) (h : ∀ v∈rows, v.passes=true) :
    summedJumpWord rows=packedSum spatialBase 641 (fun i => totalJump rows i+2^63) := by
  rw [summedJumpWord,packedSum_add,packedSum_const (by decide : 1<spatialBase)]
  apply congrArg (fun x : ℤ => x+2^63*packedOnes spatialBase 641)
  induction rows with
  | nil => simp [totalJump,packedSum]
  | cons v vs ih =>
    have hv := (v.sound (h _ (by simp))).1.trans (packEval_eq _ _ _)
    have ht := ih (fun u hu => h _ (List.mem_cons_of_mem _ hu))
    change v.packed+(vs.map SpatialLane.packed).sum=packedSum spatialBase 641 (fun i => v.jump i+totalJump vs i)
    rw [packedSum_add,hv,ht]

theorem summedJumpAt_eq (rows : List SpatialLane) (h : ∀ v∈rows, v.passes=true) (hb : jumpBudget rows≤10^13)
    {i : ℕ} (hi : i<641) : summedJumpAt (summedJumpWord rows) i=totalJump rows i := by
  have ht (k : ℕ) (hk : k<641) := abs_le.mp ((abs_le_range_sum (totalJump rows) hk).trans ((totalJump_norm rows h).trans hb))
  rw [summedJumpAt,summedJumpWord_eq rows h,packedDigit_eq (by decide : 0<spatialBase) _ (fun k hk => ?_) hi]
  · omega
  · have H := ht k hk
    unfold spatialBase
    constructor <;> omega

def summedResidual (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ) :=
  let a := summedJumpAt (summedJumpWord rows)
  let edge := bandJumpWord energyBase ws
  lagEnergyWord 80001 (edge-coarseWord (energyBase^125) a)
    (-edge-coarseWord (energyBase^125) (fun j => a (640-j))) basis.word (-1)

theorem residualEnergy_summed (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ)
    (checked : rows.all SpatialLane.passes=true) (budget : jumpBudget rows≤10^13) :
    residualEnergy basis rows ws=summedResidual basis rows ws := by
  have he (i : ℕ) (hi : i<641) := summedJumpAt_eq rows (List.all_eq_true.mp checked) budget hi
  have h₁ : coarseWord (energyBase^125) (totalJump rows)=coarseWord (energyBase^125) (summedJumpAt (summedJumpWord rows)) := by
    rw [coarseWord_eq,coarseWord_eq]
    exact packedSum_congr (fun i hi => (he i hi).symm)
  have h₂ : coarseWord (energyBase^125) (fun j => totalJump rows (640-j))=
      coarseWord (energyBase^125) (fun j => summedJumpAt (summedJumpWord rows) (640-j)) := by
    rw [coarseWord_eq,coarseWord_eq]
    exact packedSum_congr (fun j _ => (he (640-j) (by omega)).symm)
  simp only [residualEnergy,summedResidual,residualWord,residualReverse,h₁,h₂]

end PiPolynomialValues
