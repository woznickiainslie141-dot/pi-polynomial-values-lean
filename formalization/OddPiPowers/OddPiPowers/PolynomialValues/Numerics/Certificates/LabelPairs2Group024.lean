module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary022
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary025
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary028
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Tilted001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary031
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Tilted004
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary034

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_024_references : ∀ t∈angleLabels2_024, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary024⟩,⟨evidence2Ordinary024⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary025⟩,⟨evidence2Ordinary025⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary026⟩,⟨evidence2Ordinary026⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary027⟩,⟨evidence2Ordinary027⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary028⟩,⟨evidence2Ordinary028⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary029⟩,⟨evidence2Tilted002⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary030⟩,⟨evidence2Tilted003⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary031⟩,⟨evidence2Tilted004⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary032⟩,⟨evidence2Tilted005⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary033⟩,⟨evidence2Ordinary033⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary034⟩,⟨evidence2Ordinary034⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary035⟩,⟨evidence2Ordinary035⟩⟩
  simp

end PiPolynomialValues.Certificates
