module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceRate
public import OddPiPowers.PolynomialValues.Numerics.VariationWord
public import OddPiPowers.PolynomialValues.Numerics.AngleMixture

/-! The reference bound supplied to an angular label includes its actual
signed slopes and the price for departing from the chosen center. -/

@[expose] public section

namespace PiPolynomialValues

open FourPeriod

def signedSlopes (slopes : List ℤ) := (slopes.tail.reverse.map Neg.neg)++slopes

structure ReferenceEvidence (s : Shape) (a : AnchorPlan) (slopes : List ℤ) (p : ℤ) (B : ℚ) where
  rows : List SpatialLane
  positive : 0 < rows.length
  rowCount : rows.length=s.rows.length
  field : rows.map SpatialLane.slope=signedSlopes slopes
  checked : ∀ v∈rows, v.passes=true
  cost : continuousReferenceRate s rows positive a p≤(B : ℝ)

def referenceMeta (s : Shape) (a : AnchorPlan) (rows : List SpatialLane) (slopes : List ℤ)
    (p trap var square residual : ℤ) (B : ℚ) : Bool := decide
  (0 < rows.length ∧ rows.length=s.rows.length ∧ rows.map SpatialLane.slope=signedSlopes slopes ∧
    s.widths.length≤50 ∧ (s.widths.all (fun w => decide (w≤10000)))=true ∧
    0≤p ∧ (a.length : ℤ)*|p*400000000000|≤10^27 ∧
    200000*(s.widths.length : ℤ)+jumpBudget rows≤10^13 ∧ spatialRateQ s rows trap var square residual≤B)

def referenceEvidenceOfChecks (basis : (r : ℕ) → StripeBasis r) (E : EnergySection 641 125 0 641)
    (T : EnergySection 80001 1 0 80001) (s : Shape) (a : AnchorPlan) (rows : List SpatialLane)
    (slopes : List ℤ) (p trap var square residual : ℤ) (B : ℚ)
    (hrows : rows.all SpatialLane.passes=true) (hc : a.covers 0 80000=true)
    (hi : gridCostBlock 0 125 (fun r => quickReferenceCost rows s.widths a p r (basis r))=trap)
    (hv : fastVariation rows=var) (he : (rows.map (regularEnergy E)).sum=square)
    (hr : residualEnergy T rows s.widths=residual) (hm : referenceMeta s a rows slopes p trap var square residual B=true) :
    ReferenceEvidence s a slopes p B := by
  obtain ⟨hn,hcount,hfield,hw,hb,hp,hbudget,hj,hB⟩ := of_decide_eq_true hm
  have hd := List.all_eq_true.mp hrows
  have H := spatial_rate_majorant basis E T s rows hn hd hw (fun w h => of_decide_eq_true (List.all_eq_true.mp hb w h))
    a hc hp hbudget hj
  rw [hi,← fastVariation_sound rows hd,hv,he,hr] at H
  exact ⟨rows,hn,hcount,hfield,hd,H.trans ((Rat.cast_le (K := ℝ)).mpr hB)⟩

end PiPolynomialValues
