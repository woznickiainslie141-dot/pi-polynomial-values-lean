module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary082
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary085
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary088
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary091
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary094

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_084_references : ∀ t∈angleLabels2_084, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary084⟩,⟨evidence2Ordinary084⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary085⟩,⟨evidence2Ordinary085⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary086⟩,⟨evidence2Ordinary086⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary087⟩,⟨evidence2Ordinary087⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary088⟩,⟨evidence2Ordinary088⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary089⟩,⟨evidence2Ordinary089⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary090⟩,⟨evidence2Ordinary090⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary091⟩,⟨evidence2Ordinary091⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary092⟩,⟨evidence2Ordinary092⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary093⟩,⟨evidence2Ordinary093⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary094⟩,⟨evidence2Ordinary094⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary095⟩,⟨evidence2Ordinary095⟩⟩
  simp

end PiPolynomialValues.Certificates
