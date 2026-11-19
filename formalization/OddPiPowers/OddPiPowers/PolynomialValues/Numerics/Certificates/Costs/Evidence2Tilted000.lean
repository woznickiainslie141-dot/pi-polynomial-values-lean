module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy2Tilted000

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation2Tilted000 : fastVariation reference2Tilted000=6674035 := by decide +kernel

theorem meta2Tilted000 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Tilted000 [0, 1500000, 3000000, 4500000] 1321 (10268608088935730619600000) 6674035 (477003536940529183958236) (-35495347690532545234) (1014343339512613390590/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Tilted000 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 1500000, 3000000, 4500000] 1321 (1014343339512613390590/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Tilted000 [0, 1500000, 3000000, 4500000] 1321 (10268608088935730619600000) 6674035 (477003536940529183958236) (-35495347690532545234) (1014343339512613390590/10^20 : ℚ)
    reference2Tilted000_checked anchorPlan2_covers trap2Tilted000 variation2Tilted000 square2Tilted000 residual2Tilted000 meta2Tilted000

end PiPolynomialValues.Certificates
