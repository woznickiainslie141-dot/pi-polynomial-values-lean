module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group012
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group024
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group048
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group060
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs3Group084

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleDesign3_references : ∀ t∈angleDesign3.labels, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  intro t ht
  simp only [angleDesign3,List.mem_append,or_assoc] at ht
  rcases ht with h|h|h|h|h|h|h|h
  · exact angleLabels3_000_references t h
  · exact angleLabels3_012_references t h
  · exact angleLabels3_024_references t h
  · exact angleLabels3_036_references t h
  · exact angleLabels3_048_references t h
  · exact angleLabels3_060_references t h
  · exact angleLabels3_072_references t h
  · exact angleLabels3_084_references t h

end PiPolynomialValues.Certificates
