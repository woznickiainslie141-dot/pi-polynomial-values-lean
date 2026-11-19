module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary046
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary049
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary052
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary055
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary058

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_048_references : ∀ t∈angleLabels2_048, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary048⟩,⟨evidence2Ordinary048⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary049⟩,⟨evidence2Ordinary049⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary050⟩,⟨evidence2Ordinary050⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary051⟩,⟨evidence2Ordinary051⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary052⟩,⟨evidence2Ordinary052⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary053⟩,⟨evidence2Ordinary053⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary054⟩,⟨evidence2Ordinary054⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary055⟩,⟨evidence2Ordinary055⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary056⟩,⟨evidence2Ordinary056⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary057⟩,⟨evidence2Ordinary057⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary058⟩,⟨evidence2Ordinary058⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary059⟩,⟨evidence2Ordinary059⟩⟩
  simp

end PiPolynomialValues.Certificates
