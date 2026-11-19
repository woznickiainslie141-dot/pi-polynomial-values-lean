module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap3Ordinary000Part000 :
    gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary000 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1134414417068076122960000 := by decide +kernel

end PiPolynomialValues.Certificates
