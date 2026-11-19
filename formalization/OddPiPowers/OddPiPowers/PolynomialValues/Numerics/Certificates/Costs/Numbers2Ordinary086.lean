module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared2Ordinary086
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary086Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary086 :
    (reference2Ordinary086.map (regularEnergy coarseEnergyBasis)).sum=380624908084911547492218 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump2Ordinary086 : (reference2Ordinary086.map SpatialLane.packed).sum=wide641 coarseJump2Ordinary086 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive2Ordinary086 : primitiveComponent fineEnergyBasis reference2Ordinary086 FourPeriod.quadraticShape.widths=-25151257530012808534 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump2Ordinary086 checkedJump2Ordinary086,primitiveInput2Ordinary086]

set_option maxRecDepth 8192 in
theorem rounding2Ordinary086 : roundingComponent reference2Ordinary086 FourPeriod.quadraticShape.widths=16503977315572 := by
  rw [roundingComponent_prepared _ _ coarseJump2Ordinary086 checkedJump2Ordinary086,roundingInput2Ordinary086]

set_option maxRecDepth 8192 in
theorem residual2Ordinary086 : residualEnergy fineEnergyBasis reference2Ordinary086 FourPeriod.quadraticShape.widths=-25151241026035492962 := by
  rw [residualEnergy_components _ _ _ reference2Ordinary086_checked (by decide +kernel),primitive2Ordinary086,rounding2Ordinary086] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary086 :
    fastVariation reference2Ordinary086=3839895 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary086 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary086 [0, 713159, 1417708, 2268400] 0 (-1043231137283439722000000) 3839895 (380624908084911547492218) (-25151241026035492962) (422592233445011098706/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
