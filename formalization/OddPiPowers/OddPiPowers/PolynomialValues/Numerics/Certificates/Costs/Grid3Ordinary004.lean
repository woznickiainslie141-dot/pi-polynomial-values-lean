module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap3Ordinary004Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=16679181173425173873400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary004Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=16689069683085148551480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary004Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=16702162622408255881760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary004Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=16689847360905571641040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary004Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=16678695900882048177760000 := by decide +kernel

theorem trap3Ordinary004 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary004 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=83438956740706198125440000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary004Part000 trap3Ordinary004Part025)) trap3Ordinary004Part050)) trap3Ordinary004Part075)) trap3Ordinary004Part100))

end PiPolynomialValues.Certificates
