module

public import OddPiPowers.PolynomialValues.Numerics.SpatialQuadrature

/-! The affine ramp in every field has a closed evaluation. The checker
uses this expression so that one quadrature does not rebuild an entire
power series per node and stripe. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def packedRamp (b : ℤ) (n : ℕ) := ((n : ℤ)*b^n-b*packedOnes b n)/(b-1)

theorem packedRamp_sound {b : ℤ} (hb : 1<b) (n : ℕ) :
    packedRamp b n=packEval b n (fun i => (i : ℤ)) := by
  have h (m : ℕ) : packedSum b m (fun i => (i : ℤ))*(b-1)=
      (m : ℤ)*b^m-b*packedSum b m (fun _ => 1) := by
    induction m with
    | zero => simp [packedSum]
    | succ m ih =>
      simp only [packedSum,sum_range_succ,Nat.cast_succ,pow_succ,one_mul] at ih ⊢
      linear_combination ih
  rw [packedRamp,packedOnes_eq hb,← h,Int.mul_ediv_cancel _ (by omega),packEval_eq]

def PricedSpatialLane.quickWord (p : PricedSpatialLane) (r : ℕ) (basis : StripeBasis r) :=
  let v := p.lane
  let n := stripeCount r
  let ones := packedOnes spatialBase n
  let pot := stripePotential r basis.word v.packed
  40000*(pot+(-v.β*10^9+2*v.norm)*ones)+
    10^9*v.slope*(((r : ℤ)-40000)*ones+125*packedRamp spatialBase n)+p.surcharge.word spatialBase r n

theorem PricedSpatialLane.quickWord_eq (p : PricedSpatialLane) (r : ℕ) (basis : StripeBasis r) :
    p.quickWord r basis=p.word r basis := by
  simp only [quickWord,word,SpatialLane.word,fieldWord,packedRamp_sound (by decide : 1<spatialBase)]

def quickStripeCost (rows : List PricedSpatialLane) (w : GridWeights) (r : ℕ) (basis : StripeBasis r) :=
  packedDot spatialBase spatialBias (stripeCount r)
    (packedMaxList 127 (stripeCount r) (10^28) (fun p => p.quickWord r basis) rows)
    (w.reversedWord spatialBase r (stripeCount r))

theorem quickStripeCost_eq (rows : List PricedSpatialLane) (w : GridWeights) (r : ℕ) (basis : StripeBasis r) :
    quickStripeCost rows w r basis=stripeWeightedCost rows w r basis := by
  simp only [quickStripeCost,stripeWeightedCost,stripeEnvelope,PricedSpatialLane.quickWord_eq]

def quickReferenceCost (rows : List SpatialLane) (widths : List ℕ) (a : AnchorPlan) (price : ℤ)
    (r : ℕ) (basis : StripeBasis r) :=
  if price=0 then quickStripeCost (bareLanes rows) (bandWeights widths 0++bandWeights widths 1) r basis
  else
    quickStripeCost (bareLanes rows) (bandWeights (widths.take 1) 0++bandWeights (widths.take 1) 1) r basis+
    quickStripeCost (feeLanes rows a 0 price) (bandWeights widths.tail 0) r basis+
    quickStripeCost (feeLanes rows a 1 price) (bandWeights widths.tail 1) r basis

theorem quickReferenceCost_eq (rows : List SpatialLane) (widths : List ℕ) (a : AnchorPlan) (price : ℤ)
    (r : ℕ) (basis : StripeBasis r) :
    quickReferenceCost rows widths a price r basis=referenceStripeCost rows widths a price r basis := by
  simp only [quickReferenceCost,referenceStripeCost,quickStripeCost_eq]

def gridCostBlock (start len : ℕ) (f : ℕ → ℤ) := packEval 1 len (fun k => f (start+k))

theorem gridCostBlock_eq (start len : ℕ) (f : ℕ → ℤ) :
    gridCostBlock start len f=∑ k ∈ range len, f (start+k) := packEval_one _ _

theorem gridCostBlock_join (start m n : ℕ) (f : ℕ → ℤ) :
    gridCostBlock start m f+gridCostBlock (start+m) n f=gridCostBlock start (m+n) f := by
  simp only [gridCostBlock_eq,sum_range_add,Nat.add_assoc]

end PiPolynomialValues
