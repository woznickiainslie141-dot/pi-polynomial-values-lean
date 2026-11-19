module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy2Ordinary001

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation2Ordinary001 : fastVariation reference2Ordinary001=717518 := by decide +kernel

theorem meta2Ordinary001 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary001 [0, 10000, 20000, 30000] 0 (-3541074583799786625680000) 717518 (106149871399704671857434) (-245454157550280982156) (-37541839712637502001/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary001 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 10000, 20000, 30000] 0 (-37541839712637502001/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary001 [0, 10000, 20000, 30000] 0 (-3541074583799786625680000) 717518 (106149871399704671857434) (-245454157550280982156) (-37541839712637502001/10^20 : ℚ)
    reference2Ordinary001_checked anchorPlan2_covers trap2Ordinary001 variation2Ordinary001 square2Ordinary001 residual2Ordinary001 meta2Ordinary001

end PiPolynomialValues.Certificates
