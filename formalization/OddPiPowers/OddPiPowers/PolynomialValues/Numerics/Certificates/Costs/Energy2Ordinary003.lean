module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary001
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary003 :
    (reference2Ordinary003.map (regularEnergy coarseEnergyBasis)).sum=434079422983136009459464 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary003 :
    residualEnergy fineEnergyBasis reference2Ordinary003 FourPeriod.quadraticShape.widths=-34911178332945461826 := by decide +kernel

end PiPolynomialValues.Certificates
