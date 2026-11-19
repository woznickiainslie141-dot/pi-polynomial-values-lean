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
theorem paid2Tilted000Block015Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246179904700732475920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block015Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246709183104902676240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block015Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246819743383553180560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block015Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=247165744835394404120000 := by decide +kernel

theorem paid2Tilted000Block015 : gridCostBlock 15 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=986874576024582736840000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 15 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 15 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 15 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block015Slice015 paid2Tilted000Block015Slice018)) paid2Tilted000Block015Slice021)) paid2Tilted000Block015Slice024))

end PiPolynomialValues.Certificates
