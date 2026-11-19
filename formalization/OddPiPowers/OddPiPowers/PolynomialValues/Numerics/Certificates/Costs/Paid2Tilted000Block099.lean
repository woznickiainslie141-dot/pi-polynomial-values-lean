module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block099Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=247165744835394404120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block099Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246819743383553180560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block099Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246709183104902676240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block099Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246179904700732475920000 := by decide +kernel

theorem paid2Tilted000Block099 : gridCostBlock 99 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=986874576024582736840000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 99 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 99 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 99 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block099Slice099 paid2Tilted000Block099Slice102)) paid2Tilted000Block099Slice105)) paid2Tilted000Block099Slice108))

end PiPolynomialValues.Certificates
