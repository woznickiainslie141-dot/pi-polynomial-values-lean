module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary039
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary042
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary045

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_036_references : ∀ t∈angleLabels3_036, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary036⟩,⟨evidence3Ordinary036⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary037⟩,⟨evidence3Ordinary037⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary038⟩,⟨evidence3Ordinary038⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary039⟩,⟨evidence3Ordinary039⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary040⟩,⟨evidence3Ordinary040⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary041⟩,⟨evidence3Ordinary041⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary042⟩,⟨evidence3Ordinary042⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary043⟩,⟨evidence3Ordinary043⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary044⟩,⟨evidence3Ordinary044⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary045⟩,⟨evidence3Ordinary045⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary046⟩,⟨evidence3Ordinary046⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary047⟩,⟨evidence3Ordinary047⟩⟩
  simp

end PiPolynomialValues.Certificates
