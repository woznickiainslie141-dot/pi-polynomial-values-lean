module

public import OddPiPowers.PolynomialValues.Numerics.ShiftedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem rounding3Ordinary000 :
    roundingComponent reference3Ordinary000 FourPeriod.cubicShape.widths=47086433435264 := by decide +kernel

end PiPolynomialValues.Certificates
