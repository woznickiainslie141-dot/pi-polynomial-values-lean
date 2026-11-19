module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared2Ordinary085
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.Field2Ordinary085Data
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Ordinary085 :
    (reference2Ordinary085.map (regularEnergy coarseEnergyBasis)).sum=353706023544289179895258 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump2Ordinary085 : (reference2Ordinary085.map SpatialLane.packed).sum=wide641 coarseJump2Ordinary085 := by decide +kernel

set_option maxRecDepth 8192 in
theorem primitive2Ordinary085 : primitiveComponent fineEnergyBasis reference2Ordinary085 FourPeriod.quadraticShape.widths=-20712444808228640866 := by
  rw [primitiveComponent_prepared _ _ _ coarseJump2Ordinary085 checkedJump2Ordinary085,primitiveInput2Ordinary085]

set_option maxRecDepth 8192 in
theorem rounding2Ordinary085 : roundingComponent reference2Ordinary085 FourPeriod.quadraticShape.widths=16536101517056 := by
  rw [roundingComponent_prepared _ _ coarseJump2Ordinary085 checkedJump2Ordinary085,roundingInput2Ordinary085]

set_option maxRecDepth 8192 in
theorem residual2Ordinary085 : residualEnergy fineEnergyBasis reference2Ordinary085 FourPeriod.quadraticShape.widths=-20712428272127123810 := by
  rw [residualEnergy_components _ _ _ reference2Ordinary085_checked (by decide +kernel),primitive2Ordinary085,rounding2Ordinary085] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary085 :
    fastVariation reference2Ordinary085=3451047 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary085 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary085 [0, 553051, 1152604, 1850930] 0 (-2682927575900559642480000) 3451047 (353706023544289179895258) (-20712428272127123810) (318650016156761933315/10^20 : ℚ)=true := by decide +kernel

end PiPolynomialValues.Certificates
