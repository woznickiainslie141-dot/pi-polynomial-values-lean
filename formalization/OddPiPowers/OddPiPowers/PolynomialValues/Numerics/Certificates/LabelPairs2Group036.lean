module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary034
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary037
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary040
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Tilted004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary043
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary046

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_036_references : ∀ t∈angleLabels2_036, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary036⟩,⟨evidence2Ordinary036⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary037⟩,⟨evidence2Ordinary037⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary038⟩,⟨evidence2Ordinary038⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary039⟩,⟨evidence2Ordinary039⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary040⟩,⟨evidence2Ordinary040⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary041⟩,⟨evidence2Tilted006⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary042⟩,⟨evidence2Ordinary042⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary043⟩,⟨evidence2Ordinary043⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary044⟩,⟨evidence2Ordinary044⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary045⟩,⟨evidence2Ordinary045⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary046⟩,⟨evidence2Ordinary046⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary047⟩,⟨evidence2Ordinary047⟩⟩
  simp

end PiPolynomialValues.Certificates
