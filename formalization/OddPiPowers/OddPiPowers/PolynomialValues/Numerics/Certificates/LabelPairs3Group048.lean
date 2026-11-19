module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary048
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary051
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary054
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary057

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_048_references : ∀ t∈angleLabels3_048, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary048⟩,⟨evidence3Ordinary048⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary049⟩,⟨evidence3Ordinary049⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary050⟩,⟨evidence3Ordinary050⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary051⟩,⟨evidence3Ordinary051⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary052⟩,⟨evidence3Ordinary052⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary053⟩,⟨evidence3Ordinary053⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary054⟩,⟨evidence3Ordinary054⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary055⟩,⟨evidence3Ordinary055⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary056⟩,⟨evidence3Ordinary056⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary057⟩,⟨evidence3Ordinary057⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary058⟩,⟨evidence3Ordinary058⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary059⟩,⟨evidence3Ordinary059⟩⟩
  simp

end PiPolynomialValues.Certificates
