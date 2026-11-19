module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign2
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary010
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary013
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary016
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary019
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch2Ordinary022

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels2_012_references : ∀ t∈angleLabels2_012, LabelReferencePair FourPeriod.quadraticShape anchorPlan2 t := by
  apply labelPairs_cons ⟨⟨evidence2Ordinary012⟩,⟨evidence2Ordinary012⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary013⟩,⟨evidence2Ordinary013⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary014⟩,⟨evidence2Ordinary014⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary015⟩,⟨evidence2Ordinary015⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary016⟩,⟨evidence2Ordinary016⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary017⟩,⟨evidence2Ordinary017⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary018⟩,⟨evidence2Ordinary018⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary019⟩,⟨evidence2Ordinary019⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary020⟩,⟨evidence2Ordinary020⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary021⟩,⟨evidence2Ordinary021⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary022⟩,⟨evidence2Ordinary022⟩⟩
  apply labelPairs_cons ⟨⟨evidence2Ordinary023⟩,⟨evidence2Ordinary023⟩⟩
  simp

end PiPolynomialValues.Certificates
