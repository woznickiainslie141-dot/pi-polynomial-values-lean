module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary003 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary003 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=4030165479917094717360000 := by decide +kernel

end PiPolynomialValues.Certificates
