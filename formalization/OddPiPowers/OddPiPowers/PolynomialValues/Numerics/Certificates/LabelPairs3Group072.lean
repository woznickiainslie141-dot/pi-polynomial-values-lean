module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary075
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary078
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary081

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_072_references : ∀ t∈angleLabels3_072, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary072⟩,⟨evidence3Ordinary072⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary073⟩,⟨evidence3Ordinary073⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary074⟩,⟨evidence3Ordinary074⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary075⟩,⟨evidence3Ordinary075⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary076⟩,⟨evidence3Ordinary076⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary077⟩,⟨evidence3Ordinary077⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary078⟩,⟨evidence3Ordinary078⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary079⟩,⟨evidence3Ordinary079⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary080⟩,⟨evidence3Ordinary080⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary081⟩,⟨evidence3Ordinary081⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary082⟩,⟨evidence3Ordinary082⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary083⟩,⟨evidence3Ordinary083⟩⟩
  simp

end PiPolynomialValues.Certificates
