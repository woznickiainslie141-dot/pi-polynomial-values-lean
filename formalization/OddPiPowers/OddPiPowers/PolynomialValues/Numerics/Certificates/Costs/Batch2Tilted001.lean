module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted003

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Tilted001 :
    (reference2Tilted001.map (regularEnergy coarseEnergyBasis)).sum=521814944338841518254394 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted001 :
    residualEnergy fineEnergyBasis reference2Tilted001 FourPeriod.quadraticShape.widths=-10316343520926229466 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted001_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted001 :
    fastVariation reference2Tilted001=6688481 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted001 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted001 [0, 2100000, 4200000, 6300000] 4107 (20337589434235208609920000) 6688481 (521814944338841518254394) (-10316343520926229466) (1490079998045856419586/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted001 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 2100000, 4200000, 6300000] 4107 (1490079998045856419586/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted001 [0, 2100000, 4200000, 6300000] 4107 (20337589434235208609920000) 6688481 (521814944338841518254394) (-10316343520926229466) (1490079998045856419586/10^20 : ℚ)
    reference2Tilted001_checked anchorPlan2_covers trap2Tilted001 variation2Tilted001 square2Tilted001 residual2Tilted001 meta2Tilted001

set_option maxRecDepth 8192 in
theorem square2Tilted002 :
    (reference2Tilted002.map (regularEnergy coarseEnergyBasis)).sum=451415931423167542967046 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted002 :
    residualEnergy fineEnergyBasis reference2Tilted002 FourPeriod.quadraticShape.widths=-37324177126325161214 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted002_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted002 :
    fastVariation reference2Tilted002=7603307 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted002 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted002 [0, 1215377, 2440366, 3750839] 350 (5940772419813919991360000) 7603307 (451415931423167542967046) (-37324177126325161214) (808111397895001400368/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted002 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1215377, 2440366, 3750839] 350 (808111397895001400368/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted002 [0, 1215377, 2440366, 3750839] 350 (5940772419813919991360000) 7603307 (451415931423167542967046) (-37324177126325161214) (808111397895001400368/10^20 : ℚ)
    reference2Tilted002_checked anchorPlan2_covers trap2Tilted002 variation2Tilted002 square2Tilted002 residual2Tilted002 meta2Tilted002

set_option maxRecDepth 8192 in
theorem square2Tilted003 :
    (reference2Tilted003.map (regularEnergy coarseEnergyBasis)).sum=483665109033925261666094 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted003 :
    residualEnergy fineEnergyBasis reference2Tilted003 FourPeriod.quadraticShape.widths=-22383155196813385684 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted003_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted003 :
    fastVariation reference2Tilted003=6772747 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted003 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted003 [0, 1528493, 3128467, 4731022] 1598 (11239504448796569858400000) 6772747 (483665109033925261666094) (-22383155196813385684) (1068410174355769920826/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted003 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1528493, 3128467, 4731022] 1598 (1068410174355769920826/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted003 [0, 1528493, 3128467, 4731022] 1598 (11239504448796569858400000) 6772747 (483665109033925261666094) (-22383155196813385684) (1068410174355769920826/10^20 : ℚ)
    reference2Tilted003_checked anchorPlan2_covers trap2Tilted003 variation2Tilted003 square2Tilted003 residual2Tilted003 meta2Tilted003

end PiPolynomialValues.Certificates
