module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy2Ordinary002

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation2Ordinary002 : fastVariation reference2Ordinary002=753924 := by decide +kernel

theorem meta2Ordinary002 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary002 [0, 4000, 8000, 12000] 0 (-3518890610661464520560000) 753924 (105341164583275402460370) (-245301495625325152530) (-37830620129319823467/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary002 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 4000, 8000, 12000] 0 (-37830620129319823467/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary002 [0, 4000, 8000, 12000] 0 (-3518890610661464520560000) 753924 (105341164583275402460370) (-245301495625325152530) (-37830620129319823467/10^20 : ℚ)
    reference2Ordinary002_checked anchorPlan2_covers trap2Ordinary002 variation2Ordinary002 square2Ordinary002 residual2Ordinary002 meta2Ordinary002

end PiPolynomialValues.Certificates
