module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Grid3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Numbers3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Grid3Ordinary004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Numbers3Ordinary004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Grid3Ordinary005
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Numbers3Ordinary005

@[expose] public section

namespace PiPolynomialValues.Certificates

noncomputable def evidence3Ordinary003 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 1500000, 3000000, 4500000, 6000000, 7500000, 9000000] 0 (1958177639689298977556/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary003 [0, 1500000, 3000000, 4500000, 6000000, 7500000, 9000000] 0 (51373281516324738034480000) 10971235 (911983563084941374392026) (-4125217577780275774) (1958177639689298977556/10^20 : ℚ)
    reference3Ordinary003_checked anchorPlan3_covers trap3Ordinary003 variation3Ordinary003 square3Ordinary003 residual3Ordinary003 meta3Ordinary003

noncomputable def evidence3Ordinary004 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 0 (2820091734119491973434/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary004 [0, 2100000, 4200000, 6300000, 8400000, 10500000, 12600000] 0 (83438956740706198125440000) 13757499 (993084699091384627871318) (-3447319416653775370) (2820091734119491973434/10^20 : ℚ)
    reference3Ordinary004_checked anchorPlan3_covers trap3Ordinary004 variation3Ordinary004 square3Ordinary004 residual3Ordinary004 meta3Ordinary004

noncomputable def evidence3Ordinary005 : ReferenceEvidence FourPeriod.cubicShape anchorPlan3 [0, 29000, 58000, 87000, 116000, 145000, 174000] 0 (-26394821839960509018/10^20 : ℚ) :=
  referenceEvidenceOfChecks spatialBasis coarseEnergyBasis fineEnergyBasis FourPeriod.cubicShape anchorPlan3 reference3Ordinary005 [0, 29000, 58000, 87000, 116000, 145000, 174000] 0 (-6439484045977008663040000) 1358356 (202951443993424753113342) (-3939556417718522090) (-26394821839960509018/10^20 : ℚ)
    reference3Ordinary005_checked anchorPlan3_covers trap3Ordinary005 variation3Ordinary005 square3Ordinary005 residual3Ordinary005 meta3Ordinary005

end PiPolynomialValues.Certificates
