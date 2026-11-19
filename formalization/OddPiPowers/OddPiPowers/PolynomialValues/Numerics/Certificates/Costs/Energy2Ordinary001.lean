module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary001
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary001 :
    (reference2Ordinary001.map (regularEnergy coarseEnergyBasis)).sum=106149871399704671857434 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary001 :
    residualEnergy fineEnergyBasis reference2Ordinary001 FourPeriod.quadraticShape.widths=-245454157550280982156 := by decide +kernel

end PiPolynomialValues.Certificates
