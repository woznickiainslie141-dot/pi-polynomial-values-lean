module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap3Ordinary005Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1288103466528670037960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary005Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1287859465565393172200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary005Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1287579165424180941120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary005Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1287835534702721292680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary005Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1288106413756043219080000 := by decide +kernel

theorem trap3Ordinary005 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary005 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-6439484045977008663040000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary005Part000 trap3Ordinary005Part025)) trap3Ordinary005Part050)) trap3Ordinary005Part075)) trap3Ordinary005Part100))

end PiPolynomialValues.Certificates
