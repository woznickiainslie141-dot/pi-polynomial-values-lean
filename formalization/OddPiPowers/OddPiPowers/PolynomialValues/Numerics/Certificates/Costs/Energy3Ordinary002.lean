module

public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy
public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary000
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Ordinary002 :
    (reference3Ordinary002.map (regularEnergy coarseEnergyBasis)).sum=842311448672591353904912 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Ordinary002 :
    residualEnergy fineEnergyBasis reference3Ordinary002 FourPeriod.cubicShape.widths=-5303659034538465608 := by
  rw [residualEnergy_summed _ _ _ reference3Ordinary002_checked (by decide +kernel)]
  decide +kernel

end PiPolynomialValues.Certificates
