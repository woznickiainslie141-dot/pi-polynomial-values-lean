module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Primitive3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Rounding3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Ordinary000 :
    (reference3Ordinary000.map (regularEnergy coarseEnergyBasis)).sum=167969120417516063851396 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Ordinary000 :
    residualEnergy fineEnergyBasis reference3Ordinary000 FourPeriod.cubicShape.widths=-3809645866747932360 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary000_checked (by decide +kernel),primitive3Ordinary000,rounding3Ordinary000] <;> decide +kernel

end PiPolynomialValues.Certificates
