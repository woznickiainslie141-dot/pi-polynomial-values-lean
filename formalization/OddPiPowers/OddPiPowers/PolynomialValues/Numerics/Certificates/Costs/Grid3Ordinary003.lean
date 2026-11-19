module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap3Ordinary003Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=10268565079209543017400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary003Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=10275567587067355799000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary003Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=10284796877611774714000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary003Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=10276122556464731185360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary003Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=10268229415971333318720000 := by decide +kernel

theorem trap3Ordinary003 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary003 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=51373281516324738034480000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary003Part000 trap3Ordinary003Part025)) trap3Ordinary003Part050)) trap3Ordinary003Part075)) trap3Ordinary003Part100))

end PiPolynomialValues.Certificates
