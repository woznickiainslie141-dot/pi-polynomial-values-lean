module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap3Ordinary001Part100 :
    gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary001 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1161437682395485720960000 := by decide +kernel

end PiPolynomialValues.Certificates
