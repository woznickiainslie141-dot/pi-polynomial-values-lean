module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Ordinary000

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem zeroMeta2 : referenceMeta FourPeriod.quadraticShape anchorPlan2 reference2Ordinary000 [0, 0, 0, 0] 0 (-3515078167381754909360000) 708218 (105183102342281770110452) (-245342834886139643884) quadraticRateData.ordinary=true := by decide +kernel

noncomputable def zeroOrdinary2 :
    ReferenceEvidence FourPeriod.quadraticShape anchorPlan2 [0, 0, 0, 0] 0 quadraticRateData.ordinary :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.quadraticShape anchorPlan2 reference2Ordinary000 [0, 0, 0, 0] 0 (-3515078167381754909360000) 708218 (105183102342281770110452) (-245342834886139643884) quadraticRateData.ordinary
    reference2Ordinary000_checked anchorPlan2_covers trap2Ordinary000 variation2Ordinary000 square2Ordinary000 residual2Ordinary000 zeroMeta2

end PiPolynomialValues.Certificates
