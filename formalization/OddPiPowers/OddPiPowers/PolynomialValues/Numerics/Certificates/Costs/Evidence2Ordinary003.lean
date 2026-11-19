module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy2Ordinary003

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation2Ordinary003 : fastVariation reference2Ordinary003=8562271 := by decide +kernel

theorem meta2Ordinary003 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary003 [0, 1100000, 2200000, 3300000] 0 (4030165479917094717360000) 8562271 (434079422983136009459464) (-34911178332945461826) (701145821054418467143/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary003 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1100000, 2200000, 3300000] 0 (701145821054418467143/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary003 [0, 1100000, 2200000, 3300000] 0 (4030165479917094717360000) 8562271 (434079422983136009459464) (-34911178332945461826) (701145821054418467143/10^20 : ℚ)
    reference2Ordinary003_checked anchorPlan2_covers trap2Ordinary003 variation2Ordinary003 square2Ordinary003 residual2Ordinary003 meta2Ordinary003

end PiPolynomialValues.Certificates
