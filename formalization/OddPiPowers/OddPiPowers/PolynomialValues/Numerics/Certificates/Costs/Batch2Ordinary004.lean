module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary004

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary004 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary004 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=10268669877289668370720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary004 :
    (reference2Ordinary004.map (regularEnergy coarseEnergyBasis)).sum=476895620464753797512246 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary004 :
    residualEnergy fineEnergyBasis reference2Ordinary004 FourPeriod.quadraticShape.widths=-38130551488756518606 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary004_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary004 :
    fastVariation reference2Ordinary004=6553949 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary004 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary004 [0, 1500000, 3000000, 4500000] 0 (10268669877289668370720000) 6553949 (476895620464753797512246) (-38130551488756518606) (1014338344320466466690/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary004 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1500000, 3000000, 4500000] 0 (1014338344320466466690/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary004 [0, 1500000, 3000000, 4500000] 0 (10268669877289668370720000) 6553949 (476895620464753797512246) (-38130551488756518606) (1014338344320466466690/10^20 : ℚ)
    reference2Ordinary004_checked anchorPlan2_covers trap2Ordinary004 variation2Ordinary004 square2Ordinary004 residual2Ordinary004 meta2Ordinary004

set_option maxRecDepth 8192 in
theorem trap2Ordinary005 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary005 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=20335398143210673952960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary005 :
    (reference2Ordinary005.map (regularEnergy coarseEnergyBasis)).sum=521735903961712402286972 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary005 :
    residualEnergy fineEnergyBasis reference2Ordinary005 FourPeriod.quadraticShape.widths=-11208433086902039160 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary005_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary005 :
    fastVariation reference2Ordinary005=6772159 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary005 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary005 [0, 2100000, 4200000, 6300000] 0 (20335398143210673952960000) 6772159 (521735903961712402286972) (-11208433086902039160) (1490065879391697367423/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary005 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 2100000, 4200000, 6300000] 0 (1490065879391697367423/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary005 [0, 2100000, 4200000, 6300000] 0 (20335398143210673952960000) 6772159 (521735903961712402286972) (-11208433086902039160) (1490065879391697367423/10^20 : ℚ)
    reference2Ordinary005_checked anchorPlan2_covers trap2Ordinary005 variation2Ordinary005 square2Ordinary005 residual2Ordinary005 meta2Ordinary005

set_option maxRecDepth 8192 in
theorem trap2Ordinary006 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary006 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-3717000379623556935920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary006 :
    (reference2Ordinary006.map (regularEnergy coarseEnergyBasis)).sum=112533268808718741448290 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary006 :
    residualEnergy fineEnergyBasis reference2Ordinary006 FourPeriod.quadraticShape.widths=-245222584159066232314 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary006_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary006 :
    fastVariation reference2Ordinary006=896040 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary006 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary006 [0, 29000, 58000, 87000] 0 (-3717000379623556935920000) 896040 (112533268808718741448290) (-245222584159066232314) (-35102864343642345560/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary006 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 29000, 58000, 87000] 0 (-35102864343642345560/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary006 [0, 29000, 58000, 87000] 0 (-3717000379623556935920000) 896040 (112533268808718741448290) (-245222584159066232314) (-35102864343642345560/10^20 : ℚ)
    reference2Ordinary006_checked anchorPlan2_covers trap2Ordinary006 variation2Ordinary006 square2Ordinary006 residual2Ordinary006 meta2Ordinary006

end PiPolynomialValues.Certificates
