module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Tilted000 :
    (reference2Tilted000.map (regularEnergy coarseEnergyBasis)).sum=477003536940529183958236 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted000 :
    residualEnergy fineEnergyBasis reference2Tilted000 FourPeriod.quadraticShape.widths=-35495347690532545234 := by decide +kernel

end PiPolynomialValues.Certificates
