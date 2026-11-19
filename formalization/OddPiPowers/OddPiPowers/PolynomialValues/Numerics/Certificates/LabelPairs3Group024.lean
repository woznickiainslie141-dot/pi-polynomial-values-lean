module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary024
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary027
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary030
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary033

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_024_references : ∀ t∈angleLabels3_024, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary024⟩,⟨evidence3Ordinary024⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary025⟩,⟨evidence3Ordinary025⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary026⟩,⟨evidence3Ordinary026⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary027⟩,⟨evidence3Ordinary027⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary028⟩,⟨evidence3Ordinary028⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary029⟩,⟨evidence3Ordinary029⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary030⟩,⟨evidence3Tilted002⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary031⟩,⟨evidence3Tilted003⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary032⟩,⟨evidence3Ordinary032⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary033⟩,⟨evidence3Ordinary033⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary034⟩,⟨evidence3Ordinary034⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary035⟩,⟨evidence3Ordinary035⟩⟩
  simp

end PiPolynomialValues.Certificates
