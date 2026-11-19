module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Reference2Ordinary000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary000 :
    (reference2Ordinary000.map (regularEnergy coarseEnergyBasis)).sum=105183102342281770110452 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary000 :
    residualEnergy fineEnergyBasis reference2Ordinary000 FourPeriod.quadraticShape.widths=-245342834886139643884 := by decide +kernel

end PiPolynomialValues.Certificates
