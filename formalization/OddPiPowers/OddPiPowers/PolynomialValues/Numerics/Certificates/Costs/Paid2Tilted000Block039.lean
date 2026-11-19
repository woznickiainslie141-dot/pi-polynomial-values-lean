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
theorem paid2Tilted000Block039Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482288567203817240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block039Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482141534898620000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block039Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482004545673672080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block039Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246481884576801495680000 := by decide +kernel

theorem paid2Tilted000Block039 : gridCostBlock 39 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=985928319224577605000000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 39 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 39 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 39 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block039Slice039 paid2Tilted000Block039Slice042)) paid2Tilted000Block039Slice045)) paid2Tilted000Block039Slice048))

end PiPolynomialValues.Certificates
