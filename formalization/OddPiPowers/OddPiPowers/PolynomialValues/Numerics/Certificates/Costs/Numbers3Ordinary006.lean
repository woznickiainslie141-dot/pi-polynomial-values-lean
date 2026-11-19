module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Ordinary006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Ordinary007
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Ordinary008

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Numbers3Ordinary006. -/
set_option maxRecDepth 8192 in
theorem square3Ordinary006 :
    (reference3Ordinary006.map (regularEnergy coarseEnergyBasis)).sum=271488259339021483988616 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Ordinary006 : (reference3Ordinary006.map SpatialLane.packed).sum=wide641 coarseJump3Ordinary006 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary006 : primitiveComponent fineEnergyBasis reference3Ordinary006 FourPeriod.cubicShape.widths=-3024663239112201052 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump3Ordinary006 checkedJump3Ordinary006,primitiveInput3Ordinary006]

set_option maxRecDepth 8192 in
theorem rounding3Ordinary006 : roundingComponent reference3Ordinary006 FourPeriod.cubicShape.widths=47044728439248 := by
  rw [roundingComponent_prepared _ _ coarseJump3Ordinary006 checkedJump3Ordinary006,roundingInput3Ordinary006]

set_option maxRecDepth 8192 in
theorem residual3Ordinary006 : residualEnergy fineEnergyBasis reference3Ordinary006 FourPeriod.cubicShape.widths=-3024616194383761804 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary006_checked (by decide +kernel),primitive3Ordinary006,rounding3Ordinary006] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary006 :
    fastVariation reference3Ordinary006=1942929 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary006 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary006 [0, 62000, 124000, 186000, 248000, 310000, 372000] 0 (-7464268074122205915360000) 1942929 (271488259339021483988616) (-3024616194383761804) (-2457647955948371064/10^20 : ℚ)=true := by decide +kernel
/- Independently checkable declarations from Numbers3Ordinary007. -/
set_option maxRecDepth 8192 in
theorem square3Ordinary007 :
    (reference3Ordinary007.map (regularEnergy coarseEnergyBasis)).sum=1166770933757941339599172 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Ordinary007 : (reference3Ordinary007.map SpatialLane.packed).sum=wide641 coarseJump3Ordinary007 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary007 : primitiveComponent fineEnergyBasis reference3Ordinary007 FourPeriod.cubicShape.widths=-1526065484705192306 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump3Ordinary007 checkedJump3Ordinary007,primitiveInput3Ordinary007]

set_option maxRecDepth 8192 in
theorem rounding3Ordinary007 : roundingComponent reference3Ordinary007 FourPeriod.cubicShape.widths=51106363420772 := by
  rw [roundingComponent_prepared _ _ coarseJump3Ordinary007 checkedJump3Ordinary007,roundingInput3Ordinary007]

set_option maxRecDepth 8192 in
theorem residual3Ordinary007 : residualEnergy fineEnergyBasis reference3Ordinary007 FourPeriod.cubicShape.widths=-1526014378341771534 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary007_checked (by decide +kernel),primitive3Ordinary007,rounding3Ordinary007] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary007 :
    fastVariation reference3Ordinary007=20436079 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary007 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary007 [0, 4500000, 9000000, 13500000, 18000000, 22500000, 27000000] 0 (216955542167067004984240000) 20436079 (1166770933757941339599172) (-1526014378341771534) (6295632401041781085435/10^20 : ℚ)=true := by decide +kernel
/- Independently checkable declarations from Numbers3Ordinary008. -/
set_option maxRecDepth 8192 in
theorem square3Ordinary008 :
    (reference3Ordinary008.map (regularEnergy coarseEnergyBasis)).sum=767991085245971412651248 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Ordinary008 : (reference3Ordinary008.map SpatialLane.packed).sum=wide641 coarseJump3Ordinary008 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive3Ordinary008 : primitiveComponent fineEnergyBasis reference3Ordinary008 FourPeriod.cubicShape.widths=-5901853126386086638 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump3Ordinary008 checkedJump3Ordinary008,primitiveInput3Ordinary008]

set_option maxRecDepth 8192 in
theorem rounding3Ordinary008 : roundingComponent reference3Ordinary008 FourPeriod.cubicShape.widths=46564609609620 := by
  rw [roundingComponent_prepared _ _ coarseJump3Ordinary008 checkedJump3Ordinary008,roundingInput3Ordinary008]

set_option maxRecDepth 8192 in
theorem residual3Ordinary008 : residualEnergy fineEnergyBasis reference3Ordinary008 FourPeriod.cubicShape.widths=-5901806561776477018 := by
  rw [residualEnergy_components _ _ _ reference3Ordinary008_checked (by decide +kernel),primitive3Ordinary008,rounding3Ordinary008] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Ordinary008 :
    fastVariation reference3Ordinary008=7702904 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Ordinary008 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary008 [0, 800000, 1600000, 2400000, 3200000, 4000000, 4800000] 0 (15897022216714940065120000) 7702904 (767991085245971412651248) (-5901806561776477018) (963911678225407223444/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
