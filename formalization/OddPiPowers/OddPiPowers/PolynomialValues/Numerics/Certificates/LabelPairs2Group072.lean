module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary070
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary073
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary076
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary079
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary082

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_072_references : ∀ t∈angleLabels2_072, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary072⟩,⟨evidence2Ordinary072⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary073⟩,⟨evidence2Ordinary073⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary074⟩,⟨evidence2Ordinary074⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary075⟩,⟨evidence2Ordinary075⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary076⟩,⟨evidence2Ordinary076⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary077⟩,⟨evidence2Ordinary077⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary078⟩,⟨evidence2Ordinary078⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary079⟩,⟨evidence2Ordinary079⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary080⟩,⟨evidence2Ordinary080⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary081⟩,⟨evidence2Ordinary081⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary082⟩,⟨evidence2Ordinary082⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary083⟩,⟨evidence2Ordinary083⟩⟩
  simp

end PiPolynomialValues.Certificates
