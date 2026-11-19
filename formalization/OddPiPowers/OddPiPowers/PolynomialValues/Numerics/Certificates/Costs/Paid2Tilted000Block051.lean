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
theorem paid2Tilted000Block051Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246481763821493861600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block051Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246481656107896487760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block051Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246481558965919266800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block051Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246481461919850705520000 := by decide +kernel

theorem paid2Tilted000Block051 : gridCostBlock 51 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=985926440815160321680000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 51 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 51 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 51 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block051Slice051 paid2Tilted000Block051Slice054)) paid2Tilted000Block051Slice057)) paid2Tilted000Block051Slice060))

end PiPolynomialValues.Certificates
