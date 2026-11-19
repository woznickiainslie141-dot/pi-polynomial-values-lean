module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence3Ordinary000

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem zeroMeta3 : referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary000 [0, 0, 0, 0, 0, 0, 0] 0 (-5671210277818764078800000) 679588 (167969120417516063851396) (-3809645866747932360) cubicRateData.ordinary=true := by decide +kernel

noncomputable def zeroOrdinary3 :
    ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 0, 0, 0, 0, 0, 0] 0 cubicRateData.ordinary :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary000 [0, 0, 0, 0, 0, 0, 0] 0 (-5671210277818764078800000) 679588 (167969120417516063851396) (-3809645866747932360) cubicRateData.ordinary
    reference3Ordinary000_checked anchorPlan3_covers trap3Ordinary000 variation3Ordinary000 square3Ordinary000 residual3Ordinary000 zeroMeta3

end PiPolynomialValues.Certificates
