module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary058
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary061
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary064
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary067
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary070

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_060_references : ∀ t∈angleLabels2_060, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary060⟩,⟨evidence2Ordinary060⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary061⟩,⟨evidence2Ordinary061⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary062⟩,⟨evidence2Ordinary062⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary063⟩,⟨evidence2Ordinary063⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary064⟩,⟨evidence2Ordinary064⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary065⟩,⟨evidence2Ordinary065⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary066⟩,⟨evidence2Ordinary066⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary067⟩,⟨evidence2Ordinary067⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary068⟩,⟨evidence2Ordinary068⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary069⟩,⟨evidence2Ordinary069⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary070⟩,⟨evidence2Ordinary070⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary071⟩,⟨evidence2Ordinary071⟩⟩
  simp

end PiPolynomialValues.Certificates
