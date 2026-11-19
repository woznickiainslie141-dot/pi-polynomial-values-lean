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
theorem square3Ordinary001 :
    (reference3Ordinary001.map (regularEnergy coarseEnergyBasis)).sum=173119809836397701478068 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Ordinary001 :
    residualEnergy fineEnergyBasis reference3Ordinary001 FourPeriod.cubicShape.widths=-2602925506509517228 := by
  rw [residualEnergy_summed _ _ _ reference3Ordinary001_checked (by decide +kernel)]
  decide +kernel

end PiPolynomialValues.Certificates
