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
theorem paid2Tilted000Block027Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246692807350656610000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block027Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482953510487368320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block027Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482721664722610840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted000Block027Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=246482521655295692320000 := by decide +kernel

theorem paid2Tilted000Block027 : gridCostBlock 27 12 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=986141004181162281480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 27 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 27 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 27 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block027Slice027 paid2Tilted000Block027Slice030)) paid2Tilted000Block027Slice033)) paid2Tilted000Block027Slice036))

end PiPolynomialValues.Certificates
