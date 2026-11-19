module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Tilted001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Prepared3Tilted002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Tilted001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Tilted002

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square3Tilted000 :
    (reference3Tilted000.map (regularEnergy coarseEnergyBasis)).sum=993071848962954509499194 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Tilted000 : (reference3Tilted000.map SpatialLane.packed).sum=wide641 coarseJump3Tilted000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Tilted000 :
    residualEnergy fineEnergyBasis reference3Tilted000 FourPeriod.cubicShape.widths=-3433505438161272808 := by
  rw [residualEnergy_components _ _ _ reference3Tilted000_checked (by decide +kernel),
    primitiveComponent_prepared _ _ _ coarseJump3Tilted000 checkedJump3Tilted000, primitiveInput3Tilted000,
    roundingComponent_prepared _ _ coarseJump3Tilted000 checkedJump3Tilted000, roundingInput3Tilted000] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Tilted000 :
    fastVariation reference3Tilted000=13754508 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Tilted000 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Tilted000 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 151 (83439293116663881787440000) 13754508 (993071848962954509499194) (-3433505438161272808) (2820092309204099510805/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Tilted000 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 151 (2820092309204099510805/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Tilted000 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 151 (83439293116663881787440000) 13754508 (993071848962954509499194) (-3433505438161272808) (2820092309204099510805/10^20 : ℚ)
    reference3Tilted000_checked anchorPlan3_covers trap3Tilted000 variation3Tilted000 square3Tilted000 residual3Tilted000 meta3Tilted000

set_option maxRecDepth 8192 in
theorem square3Tilted001 :
    (reference3Tilted001.map (regularEnergy coarseEnergyBasis)).sum=1166620450984765136583072 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Tilted001 : (reference3Tilted001.map SpatialLane.packed).sum=wide641 coarseJump3Tilted001 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Tilted001 :
    residualEnergy fineEnergyBasis reference3Tilted001 FourPeriod.cubicShape.widths=-1629599834638177630 := by
  rw [residualEnergy_components _ _ _ reference3Tilted001_checked (by decide +kernel),
    primitiveComponent_prepared _ _ _ coarseJump3Tilted001 checkedJump3Tilted001, primitiveInput3Tilted001,
    roundingComponent_prepared _ _ coarseJump3Tilted001 checkedJump3Tilted001, roundingInput3Tilted001] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Tilted001 :
    fastVariation reference3Tilted001=20994354 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Tilted001 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Tilted001 [0, 4500000, 9000000, 13500000, 18000000, 22500000, 27000000] 20119 (216962760094665335523120000) 20994354 (1166620450984765136583072) (-1629599834638177630) (6295699049671152447513/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Tilted001 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 4500000, 9000000, 13500000, 18000000, 22500000, 27000000] 20119 (6295699049671152447513/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Tilted001 [0, 4500000, 9000000, 13500000, 18000000, 22500000, 27000000] 20119 (216962760094665335523120000) 20994354 (1166620450984765136583072) (-1629599834638177630) (6295699049671152447513/10^20 : ℚ)
    reference3Tilted001_checked anchorPlan3_covers trap3Tilted001 variation3Tilted001 square3Tilted001 residual3Tilted001 meta3Tilted001

set_option maxRecDepth 8192 in
theorem square3Tilted002 :
    (reference3Tilted002.map (regularEnergy coarseEnergyBasis)).sum=1054486762719213455471224 := by decide +kernel

set_option maxRecDepth 8192 in
theorem checkedJump3Tilted002 : (reference3Tilted002.map SpatialLane.packed).sum=wide641 coarseJump3Tilted002 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual3Tilted002 :
    residualEnergy fineEnergyBasis reference3Tilted002 FourPeriod.cubicShape.widths=-2657337084510915906 := by
  rw [residualEnergy_components _ _ _ reference3Tilted002_checked (by decide +kernel),
    primitiveComponent_prepared _ _ _ coarseJump3Tilted002 checkedJump3Tilted002, primitiveInput3Tilted002,
    roundingComponent_prepared _ _ coarseJump3Tilted002 checkedJump3Tilted002, roundingInput3Tilted002] <;> decide +kernel

set_option maxRecDepth 8192 in
theorem variation3Tilted002 :
    fastVariation reference3Tilted002=15295916 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta3Tilted002 :
    referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Tilted002 [0, 2749774, 5706972, 8612016, 11553123, 14159633, 16206111] 4447 (124466189150135732464080000) 15295916 (1054486762719213455471224) (-2657337084510915906) (3856007619918928911344/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Tilted002 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 2749774, 5706972, 8612016, 11553123, 14159633, 16206111] 4447 (3856007619918928911344/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Tilted002 [0, 2749774, 5706972, 8612016, 11553123, 14159633, 16206111] 4447 (124466189150135732464080000) 15295916 (1054486762719213455471224) (-2657337084510915906) (3856007619918928911344/10^20 : ℚ)
    reference3Tilted002_checked anchorPlan3_covers trap3Tilted002 variation3Tilted002 square3Tilted002 residual3Tilted002 meta3Tilted002

end PiPolynomialValues.Certificates
