module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary094
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary097
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary100
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary103

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_096_references : ∀ t∈angleLabels2_096, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary096⟩,⟨evidence2Ordinary096⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary097⟩,⟨evidence2Ordinary097⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary098⟩,⟨evidence2Ordinary098⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary099⟩,⟨evidence2Ordinary099⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary100⟩,⟨evidence2Ordinary100⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary101⟩,⟨evidence2Ordinary101⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary102⟩,⟨evidence2Ordinary102⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary103⟩,⟨evidence2Ordinary103⟩⟩
  simp

end PiPolynomialValues.Certificates
