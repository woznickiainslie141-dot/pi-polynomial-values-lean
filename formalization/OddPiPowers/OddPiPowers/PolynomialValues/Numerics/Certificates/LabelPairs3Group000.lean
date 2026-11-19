module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence3Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence3Ordinary001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence3Ordinary002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary009

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_000_references : ∀ t∈angleLabels3_000, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary000⟩,⟨evidence3Ordinary000⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary001⟩,⟨evidence3Ordinary001⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary002⟩,⟨evidence3Ordinary002⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary003⟩,⟨evidence3Ordinary003⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary004⟩,⟨evidence3Tilted000⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary005⟩,⟨evidence3Ordinary005⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary006⟩,⟨evidence3Ordinary006⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary007⟩,⟨evidence3Tilted001⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary008⟩,⟨evidence3Ordinary008⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary009⟩,⟨evidence3Ordinary009⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary010⟩,⟨evidence3Ordinary010⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary011⟩,⟨evidence3Ordinary011⟩⟩
  simp

end PiPolynomialValues.Certificates
