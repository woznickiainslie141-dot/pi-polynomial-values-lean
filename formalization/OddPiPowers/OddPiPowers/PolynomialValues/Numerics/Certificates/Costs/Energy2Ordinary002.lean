module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary001
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary002 :
    (reference2Ordinary002.map (regularEnergy coarseEnergyBasis)).sum=105341164583275402460370 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary002 :
    residualEnergy fineEnergyBasis reference2Ordinary002 FourPeriod.quadraticShape.widths=-245301495625325152530 := by decide +kernel

end PiPolynomialValues.Certificates
