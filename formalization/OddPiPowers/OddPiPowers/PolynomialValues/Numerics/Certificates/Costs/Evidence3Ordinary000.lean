module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy3Ordinary000

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation3Ordinary000 : fastVariation reference3Ordinary000=679588 := by decide +kernel

theorem meta3Ordinary000 : referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary000 [0, 0, 0, 0, 0, 0, 0] 0 (-5671210277818764078800000) 679588 (167969120417516063851396) (-3809645866747932360) (-34882724947890663620/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Ordinary000 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 0, 0, 0, 0, 0, 0] 0 (-34882724947890663620/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary000 [0, 0, 0, 0, 0, 0, 0] 0 (-5671210277818764078800000) 679588 (167969120417516063851396) (-3809645866747932360) (-34882724947890663620/10^20 : ℚ)
    reference3Ordinary000_checked anchorPlan3_covers trap3Ordinary000 variation3Ordinary000 square3Ordinary000 residual3Ordinary000 meta3Ordinary000

end PiPolynomialValues.Certificates
