module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group012
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group024
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group048
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group060
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group084
public import OddPiPowers.PolynomialValues.Numerics.Certificates.LabelPairs2Group096

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleDesign2_references : ∀ t∈angleDesign2.labels, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  intro t ht
  simp only [angleDesign2,List.mem_append,or_assoc] at ht
  rcases ht with h|h|h|h|h|h|h|h|h
  · exact angleLabels2_000_references t h
  · exact angleLabels2_012_references t h
  · exact angleLabels2_024_references t h
  · exact angleLabels2_036_references t h
  · exact angleLabels2_048_references t h
  · exact angleLabels2_060_references t h
  · exact angleLabels2_072_references t h
  · exact angleLabels2_084_references t h
  · exact angleLabels2_096_references t h

end PiPolynomialValues.Certificates
