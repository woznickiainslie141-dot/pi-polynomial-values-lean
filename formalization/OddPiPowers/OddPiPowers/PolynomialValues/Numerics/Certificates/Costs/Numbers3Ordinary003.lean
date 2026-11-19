module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Ordinary003 :
    (reference3Ordinary003.map (regularEnergy coarseEnergyBasis)).sum=911983563084941374392026 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Ordinary003 : (reference3Ordinary003.map SpatialLane.packed).sum=wide641 coarseJump3Ordinary003 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary003 : primitiveComponent fineEnergyBasis reference3Ordinary003 FourPeriod.cubicShape.widths=-4125264476663003862 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump3Ordinary003 checkedJump3Ordinary003,primitiveInput3Ordinary003]

set_option maxRecDepth 8192 in
theorem rounding3Ordinary003 : roundingComponent reference3Ordinary003 FourPeriod.cubicShape.widths=46898882728088 := by
  rw [roundingComponent_prepared _ _ coarseJump3Ordinary003 checkedJump3Ordinary003,roundingInput3Ordinary003]

set_option maxRecDepth 8192 in
theorem residual3Ordinary003 : residualEnergy fineEnergyBasis reference3Ordinary003 FourPeriod.cubicShape.widths=-4125217577780275774 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary003_checked (by decide +kernel),primitive3Ordinary003,rounding3Ordinary003] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary003 :
    fastVariation reference3Ordinary003=10971235 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary003 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary003 [0, 1500000, 3000000, 4500000, 6000000, 7500000, 9000000] 0 (51373281516324738034480000) 10971235 (911983563084941374392026) (-4125217577780275774) (1958177639689298977556/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
