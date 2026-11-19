module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy2Ordinary000

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation2Ordinary000 : fastVariation reference2Ordinary000=708218 := by decide +kernel

theorem meta2Ordinary000 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary000 [0, 0, 0, 0] 0 (-3515078167381754909360000) 708218 (105183102342281770110452) (-245342834886139643884) (-37886327669685317934/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence2Ordinary000 : ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 0, 0, 0] 0 (-37886327669685317934/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary000 [0, 0, 0, 0] 0 (-3515078167381754909360000) 708218 (105183102342281770110452) (-245342834886139643884) (-37886327669685317934/10^20 : ℚ)
    reference2Ordinary000_checked anchorPlan2_covers trap2Ordinary000 variation2Ordinary000 square2Ordinary000 residual2Ordinary000 meta2Ordinary000

end PiPolynomialValues.Certificates
