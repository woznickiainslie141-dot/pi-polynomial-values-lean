module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Ordinary004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Ordinary004 :
    (reference3Ordinary004.map (regularEnergy coarseEnergyBasis)).sum=993084699091384627871318 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Ordinary004 : (reference3Ordinary004.map SpatialLane.packed).sum=wide641 coarseJump3Ordinary004 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary004 : primitiveComponent fineEnergyBasis reference3Ordinary004 FourPeriod.cubicShape.widths=-3447367404024074898 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump3Ordinary004 checkedJump3Ordinary004,primitiveInput3Ordinary004]

set_option maxRecDepth 8192 in
theorem rounding3Ordinary004 : roundingComponent reference3Ordinary004 FourPeriod.cubicShape.widths=47987370299528 := by
  rw [roundingComponent_prepared _ _ coarseJump3Ordinary004 checkedJump3Ordinary004,roundingInput3Ordinary004]

set_option maxRecDepth 8192 in
theorem residual3Ordinary004 : residualEnergy fineEnergyBasis reference3Ordinary004 FourPeriod.cubicShape.widths=-3447319416653775370 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary004_checked (by decide +kernel),primitive3Ordinary004,rounding3Ordinary004] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary004 :
    fastVariation reference3Ordinary004=13757499 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary004 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary004 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 0 (83438956740706198125440000) 13757499 (993084699091384627871318) (-3447319416653775370) (2820091734119491973434/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
