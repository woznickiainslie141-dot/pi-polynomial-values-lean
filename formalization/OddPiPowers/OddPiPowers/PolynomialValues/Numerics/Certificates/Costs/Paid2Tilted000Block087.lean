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
theorem paid2Tilted000Block087Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482521655295692320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block087Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482721664722610840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block087Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482953510487368320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block087Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246692807350656610000000 := by decide +kernel

theorem paid2Tilted000Block087 : gridCostBlock 87 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=986141004181162281480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 87 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 87 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 87 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block087Slice087 paid2Tilted000Block087Slice090)) paid2Tilted000Block087Slice093)) paid2Tilted000Block087Slice096))

end PiPolynomialValues.Certificates
