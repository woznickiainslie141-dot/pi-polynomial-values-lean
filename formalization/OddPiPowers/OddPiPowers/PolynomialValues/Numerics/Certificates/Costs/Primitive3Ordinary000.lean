module

public import OddPiPowers.PolynomialValues.Numerics.ShiftedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem primitive3Ordinary000 :
    primitiveComponent fineEnergyBasis reference3Ordinary000 FourPeriod.cubicShape.widths=-3809692953181367624 := by decide +kernel

end PiPolynomialValues.Certificates
