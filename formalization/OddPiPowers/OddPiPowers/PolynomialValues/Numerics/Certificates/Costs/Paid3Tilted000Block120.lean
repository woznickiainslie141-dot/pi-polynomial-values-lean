module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002207558257093019800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=1335398958799047840720000 := by decide +kernel

theorem paid3Tilted000Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=3337606517056140860520000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block120Slice120 paid3Tilted000Block120Slice123))

end PiPolynomialValues.Certificates
