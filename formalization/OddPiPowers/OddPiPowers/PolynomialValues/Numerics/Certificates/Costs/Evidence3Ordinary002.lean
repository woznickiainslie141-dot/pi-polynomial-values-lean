module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy3Ordinary002

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation3Ordinary002 : fastVariation reference3Ordinary002=9184314 := by decide +kernel

theorem meta3Ordinary002 : referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary002 [0, 1100000, 2200000, 3300000, 4400000, 5500000, 6600000] 0 (30651583118420817163840000) 9184314 (842311448672591353904912) (-5303659034538465608) (1387677869471605223401/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Ordinary002 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 1100000, 2200000, 3300000, 4400000, 5500000, 6600000] 0 (1387677869471605223401/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary002 [0, 1100000, 2200000, 3300000, 4400000, 5500000, 6600000] 0 (30651583118420817163840000) 9184314 (842311448672591353904912) (-5303659034538465608) (1387677869471605223401/10^20 : ℚ)
    reference3Ordinary002_checked anchorPlan3_covers trap3Ordinary002 variation3Ordinary002 square3Ordinary002 residual3Ordinary002 meta3Ordinary002

end PiPolynomialValues.Certificates
