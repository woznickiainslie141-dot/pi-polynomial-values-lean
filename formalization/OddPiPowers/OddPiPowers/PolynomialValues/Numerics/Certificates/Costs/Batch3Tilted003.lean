module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Tilted003

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Tilted003 :
    (reference3Tilted003.map (regularEnergy coarseEnergyBasis)).sum=1112055623950409635537916 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Tilted003 : (reference3Tilted003.map SpatialLane.packed).sum=wide641 coarseJump3Tilted003 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Tilted003 :
    residualEnergy fineEnergyBasis reference3Tilted003 FourPeriod.cubicShape.widths=-2234192155623758582 := by
  rw [residualEnergy_components _ _ _ reference3Tilted003_checked (by decide +kernel),
    primitiveComponent_prepared _ _ _ coarseJump3Tilted003 checkedJump3Tilted003, primitiveInput3Tilted003,
    roundingComponent_prepared _ _ coarseJump3Tilted003 checkedJump3Tilted003, roundingInput3Tilted003] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Tilted003 :
    fastVariation reference3Tilted003=18949653 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Tilted003 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Tilted003 [0, 4180314, 7915810, 11335750, 14844868, 18375033, 21037092] 11676 (179023513139210207919920000) 18949653 (1112055623950409635537916) (-2234192155623758582) (5108602862285101196132/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Tilted003 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 4180314, 7915810, 11335750, 14844868, 18375033, 21037092] 11676 (5108602862285101196132/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Tilted003 [0, 4180314, 7915810, 11335750, 14844868, 18375033, 21037092] 11676 (179023513139210207919920000) 18949653 (1112055623950409635537916) (-2234192155623758582) (5108602862285101196132/10^20 : ℚ)
    reference3Tilted003_checked anchorPlan3_covers trap3Tilted003 variation3Tilted003 square3Tilted003 residual3Tilted003 meta3Tilted003

end PiPolynomialValues.Certificates
