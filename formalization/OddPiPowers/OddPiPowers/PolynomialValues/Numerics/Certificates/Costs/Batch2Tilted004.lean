module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.SummedResidual
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Fine
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Coarse
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted005
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted006

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem square2Tilted004 :
    (reference2Tilted004.map (regularEnergy coarseEnergyBasis)).sum=510204719901325799801124 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted004 :
    residualEnergy fineEnergyBasis reference2Tilted004 FourPeriod.quadraticShape.widths=-12858586605182184340 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted004_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted004 :
    fastVariation reference2Tilted004=6703686 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted004 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted004 [0, 1909129, 3912039, 5777023] 3256 (17570018632905260347440000) 6703686 (510204719901325799801124) (-12858586605182184340) (1358071893781229213651/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted004 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1909129, 3912039, 5777023] 3256 (1358071893781229213651/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted004 [0, 1909129, 3912039, 5777023] 3256 (17570018632905260347440000) 6703686 (510204719901325799801124) (-12858586605182184340) (1358071893781229213651/10^20 : ℚ)
    reference2Tilted004_checked anchorPlan2_covers trap2Tilted004 variation2Tilted004 square2Tilted004 residual2Tilted004 meta2Tilted004

set_option maxRecDepth 8192 in
theorem square2Tilted005 :
    (reference2Tilted005.map (regularEnergy coarseEnergyBasis)).sum=549891133573092066131102 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted005 :
    residualEnergy fineEnergyBasis reference2Tilted005 FourPeriod.quadraticShape.widths=-3152013867533525176 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted005_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted005 :
    fastVariation reference2Tilted005=7628837 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted005 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted005 [0, 2661144, 5262417, 7402902] 5787 (28995303564466998070640000) 7628837 (549891133573092066131102) (-3152013867533525176) (1839973728825871799012/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted005 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 2661144, 5262417, 7402902] 5787 (1839973728825871799012/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted005 [0, 2661144, 5262417, 7402902] 5787 (28995303564466998070640000) 7628837 (549891133573092066131102) (-3152013867533525176) (1839973728825871799012/10^20 : ℚ)
    reference2Tilted005_checked anchorPlan2_covers trap2Tilted005 variation2Tilted005 square2Tilted005 residual2Tilted005 meta2Tilted005

set_option maxRecDepth 8192 in
theorem square2Tilted006 :
    (reference2Tilted006.map (regularEnergy coarseEnergyBasis)).sum=499519172202068986615746 := by decide +kernel

set_option maxRecDepth 8192 in
theorem residual2Tilted006 :
    residualEnergy fineEnergyBasis reference2Tilted006 FourPeriod.quadraticShape.widths=-23014746405049681148 := by
  rw [residualEnergy_summed _ _ _ reference2Tilted006_checked (by decide +kernel)]
  decide +kernel

set_option maxRecDepth 8192 in
theorem variation2Tilted006 :
    fastVariation reference2Tilted006=6782753 := by decide +kernel

set_option maxRecDepth 8192 in
theorem meta2Tilted006 :
    referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted006 [0, 1797716, 3572885, 5352296] 2650 (15049811805235815977680000) 6782753 (499519172202068986615746) (-23014746405049681148) (1240540513879884246290/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted006 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1797716, 3572885, 5352296] 2650 (1240540513879884246290/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted006 [0, 1797716, 3572885, 5352296] 2650 (15049811805235815977680000) 6782753 (499519172202068986615746) (-23014746405049681148) (1240540513879884246290/10^20 : ℚ)
    reference2Tilted006_checked anchorPlan2_covers trap2Tilted006 variation2Tilted006 square2Tilted006 residual2Tilted006 meta2Tilted006

end PiPolynomialValues.Certificates
