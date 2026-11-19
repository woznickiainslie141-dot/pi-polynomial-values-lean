module

public import OddPiPowers.PolynomialValues.Numerics.ReferenceEvidence
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Energy3Ordinary001

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem variation3Ordinary001 : fastVariation reference3Ordinary001=963006 := by decide +kernel

theorem meta3Ordinary001 : referenceMeta FourPeriod.cubicShape anchorPlan3 reference3Ordinary001 [0, 10000, 20000, 30000, 40000, 50000, 60000] 0 (-5806291944609630912080000) 963006 (173119809836397701478068) (-2602925506509517228) (-33790349859668284652/10^20 : ℚ)=true := by decide +kernel

noncomputable def evidence3Ordinary001 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 10000, 20000, 30000, 40000, 50000, 60000] 0 (-33790349859668284652/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary001 [0, 10000, 20000, 30000, 40000, 50000, 60000] 0 (-5806291944609630912080000) 963006 (173119809836397701478068) (-2602925506509517228) (-33790349859668284652/10^20 : ℚ)
    reference3Ordinary001_checked anchorPlan3_covers trap3Ordinary001 variation3Ordinary001 square3Ordinary001 residual3Ordinary001 meta3Ordinary001

end PiPolynomialValues.Certificates
