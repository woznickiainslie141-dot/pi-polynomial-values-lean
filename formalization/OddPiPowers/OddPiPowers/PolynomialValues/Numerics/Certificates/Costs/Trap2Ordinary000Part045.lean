module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Reference2Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary000Part045 :
    gridCostBlock 45 40 (fun r => quickReferenceCost reference2Ordinary000 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-1124608995838881025280000 := by decide +kernel

end PiPolynomialValues.Certificates
