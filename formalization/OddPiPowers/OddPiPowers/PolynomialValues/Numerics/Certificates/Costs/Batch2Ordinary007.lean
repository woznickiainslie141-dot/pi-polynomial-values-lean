module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Ordinary007

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem trap2Ordinary007 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary007 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-4651573638738111762000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary007 :
    (reference2Ordinary007.map (regularEnergy coarseEnergyBasis)).sum=168915971751839074026184 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary007 :
    residualEnergy fineEnergyBasis reference2Ordinary007 FourPeriod.quadraticShape.widths=-245666131562115978176 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary007_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary007 :
    fastVariation reference2Ordinary007=1632393 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary007 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary007 [0, 116000, 232000, 348000] 0 (-4651573638738111762000000) 1632393 (168915971751839074026184) (-245666131562115978176) (-3688428618333274023/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary007 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 116000, 232000, 348000] 0 (-3688428618333274023/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary007 [0, 116000, 232000, 348000] 0 (-4651573638738111762000000) 1632393 (168915971751839074026184) (-245666131562115978176) (-3688428618333274023/10^20 : ℚ)
    reference2Ordinary007_checked anchorPlan2_covers trap2Ordinary007 variation2Ordinary007 square2Ordinary007 residual2Ordinary007 meta2Ordinary007

set_option maxRecDepth 8192 in
theorem trap2Ordinary008 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary008 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-4122313631347218972080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary008 :
    (reference2Ordinary008.map (regularEnergy coarseEnergyBasis)).sum=131781786391729931521684 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary008 :
    residualEnergy fineEnergyBasis reference2Ordinary008 FourPeriod.quadraticShape.widths=-245356658485034316516 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary008_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary008 :
    fastVariation reference2Ordinary008=1154219 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary008 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary008 [0, 62000, 124000, 186000] 0 (-4122313631347218972080000) 1154219 (131781786391729931521684) (-245356658485034316516) (-26344055351369425592/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary008 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 62000, 124000, 186000] 0 (-26344055351369425592/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary008 [0, 62000, 124000, 186000] 0 (-4122313631347218972080000) 1154219 (131781786391729931521684) (-245356658485034316516) (-26344055351369425592/10^20 : ℚ)
    reference2Ordinary008_checked anchorPlan2_covers trap2Ordinary008 variation2Ordinary008 square2Ordinary008 residual2Ordinary008 meta2Ordinary008

set_option maxRecDepth 8192 in
theorem trap2Ordinary009 :
    gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary009 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-3891346147014400833920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem square2Ordinary009 :
    (reference2Ordinary009.map (regularEnergy coarseEnergyBasis)).sum=119864748603159521200346 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Ordinary009 :
    residualEnergy fineEnergyBasis reference2Ordinary009 FourPeriod.quadraticShape.widths=-245193909400831103028 := by
  rw [residualEnergy_summed _ _ _ reference2Ordinary009_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Ordinary009 :
    fastVariation reference2Ordinary009=1095498 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Ordinary009 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary009 [0, 43000, 86000, 129000] 0 (-3891346147014400833920000) 1095498 (119864748603159521200346) (-245193909400831103028) (-32003523469519023455/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary009 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 43000, 86000, 129000] 0 (-32003523469519023455/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary009 [0, 43000, 86000, 129000] 0 (-3891346147014400833920000) 1095498 (119864748603159521200346) (-245193909400831103028) (-32003523469519023455/10^20 : ℚ)
    reference2Ordinary009_checked anchorPlan2_covers trap2Ordinary009 variation2Ordinary009 square2Ordinary009 residual2Ordinary009 meta2Ordinary009

end PiPolynomialValues.Certificates
