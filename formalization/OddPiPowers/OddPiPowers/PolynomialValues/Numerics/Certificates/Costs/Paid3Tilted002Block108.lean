module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted002Block108. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085603568624726840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985511154853330269480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985415852324343802880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985706066284141464840000 := by decide +kernel

theorem paid3Tilted002Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11941718677030440264040000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block108Slice108 paid3Tilted002Block108Slice111)) paid3Tilted002Block108Slice114)) paid3Tilted002Block108Slice117))
/- Independently checkable declarations from Paid3Tilted002Block120. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986763353347947107400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=1991997970305560694640000 := by decide +kernel

theorem paid3Tilted002Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=4978761323653507802040000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block120Slice120 paid3Tilted002Block120Slice123))

end PiPolynomialValues.Certificates
