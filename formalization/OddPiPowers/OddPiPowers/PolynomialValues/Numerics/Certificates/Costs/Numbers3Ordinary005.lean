module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.ShiftedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Ordinary005 :
    (reference3Ordinary005.map (regularEnergy coarseEnergyBasis)).sum=202951443993424753113342 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary005 : primitiveComponent fineEnergyBasis reference3Ordinary005 FourPeriod.cubicShape.widths=-3939603384730004686 := by decide +kernel

set_option maxRecDepth 8192 in
theorem rounding3Ordinary005 : roundingComponent reference3Ordinary005 FourPeriod.cubicShape.widths=46967011482596 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Ordinary005 : residualEnergy fineEnergyBasis reference3Ordinary005 FourPeriod.cubicShape.widths=-3939556417718522090 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary005_checked (by decide +kernel),primitive3Ordinary005,rounding3Ordinary005] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary005 :
    fastVariation reference3Ordinary005=1358356 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary005 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary005 [0, 29000, 58000, 87000, 116000, 145000, 174000] 0 (-6439484045977008663040000) 1358356 (202951443993424753113342) (-3939556417718522090) (-26394821839960509018/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
