module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary060
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary063
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary066
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary069

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_060_references : ∀ t∈angleLabels3_060, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary060⟩,⟨evidence3Ordinary060⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary061⟩,⟨evidence3Ordinary061⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary062⟩,⟨evidence3Ordinary062⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary063⟩,⟨evidence3Ordinary063⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary064⟩,⟨evidence3Ordinary064⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary065⟩,⟨evidence3Ordinary065⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary066⟩,⟨evidence3Ordinary066⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary067⟩,⟨evidence3Ordinary067⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary068⟩,⟨evidence3Ordinary068⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary069⟩,⟨evidence3Ordinary069⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary070⟩,⟨evidence3Ordinary070⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary071⟩,⟨evidence3Ordinary071⟩⟩
  simp

end PiPolynomialValues.Certificates
