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
theorem paid2Tilted000Block003Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=245907319897292186560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block003Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246129200845502755360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block003Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246215407959045232560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block003Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246301592810871989840000 := by decide +kernel

theorem paid2Tilted000Block003 : gridCostBlock 3 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=984553521512712164320000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 3 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block003Slice003 paid2Tilted000Block003Slice006)) paid2Tilted000Block003Slice009)) paid2Tilted000Block003Slice012))

end PiPolynomialValues.Certificates
