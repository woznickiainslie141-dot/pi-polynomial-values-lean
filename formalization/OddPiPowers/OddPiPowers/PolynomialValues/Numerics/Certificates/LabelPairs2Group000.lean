module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Ordinary000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Ordinary001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Ordinary002
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Ordinary003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Evidence2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Tilted001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary007
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary010

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_000_references : ∀ t∈angleLabels2_000, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary000⟩,⟨evidence2Ordinary000⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary001⟩,⟨evidence2Ordinary001⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary002⟩,⟨evidence2Ordinary002⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary003⟩,⟨evidence2Ordinary003⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary004⟩,⟨evidence2Tilted000⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary005⟩,⟨evidence2Tilted001⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary006⟩,⟨evidence2Ordinary006⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary007⟩,⟨evidence2Ordinary007⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary008⟩,⟨evidence2Ordinary008⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary009⟩,⟨evidence2Ordinary009⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary010⟩,⟨evidence2Ordinary010⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary011⟩,⟨evidence2Ordinary011⟩⟩
  simp

end PiPolynomialValues.Certificates
