module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared2Ordinary087
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary087Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary087 :
    (reference2Ordinary087.map (regularEnergy coarseEnergyBasis)).sum=393554225635928547436384 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump2Ordinary087 : (reference2Ordinary087.map SpatialLane.packed).sum=wide641 coarseJump2Ordinary087 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive2Ordinary087 : primitiveComponent fineEnergyBasis reference2Ordinary087 FourPeriod.quadraticShape.widths=-29530002497645012028 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump2Ordinary087 checkedJump2Ordinary087,primitiveInput2Ordinary087]

set_option maxRecDepth 8192 in
theorem rounding2Ordinary087 : roundingComponent reference2Ordinary087 FourPeriod.quadraticShape.widths=16467463386316 := by
  rw [roundingComponent_prepared _ _ coarseJump2Ordinary087 checkedJump2Ordinary087,roundingInput2Ordinary087]

set_option maxRecDepth 8192 in
theorem residual2Ordinary087 : residualEnergy fineEnergyBasis reference2Ordinary087 FourPeriod.quadraticShape.widths=-29529986030181625712 := by
  rw [residualEnergy_components _ _ _ reference2Ordinary087_checked (by decide +kernel),primitive2Ordinary087,rounding2Ordinary087] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary087 :
    fastVariation reference2Ordinary087=4142039 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary087 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary087 [0, 794648, 1581461, 2501040] 0 (-29420310235822399600000) 4142039 (393554225635928547436384) (-29529986030181625712) (482733732264439190302/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
