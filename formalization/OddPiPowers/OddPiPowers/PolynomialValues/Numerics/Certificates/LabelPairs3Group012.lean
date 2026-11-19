module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary012
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary015
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary018
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary021

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_012_references : ∀ t∈angleLabels3_012, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary012⟩,⟨evidence3Ordinary012⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary013⟩,⟨evidence3Ordinary013⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary014⟩,⟨evidence3Ordinary014⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary015⟩,⟨evidence3Ordinary015⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary016⟩,⟨evidence3Ordinary016⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary017⟩,⟨evidence3Ordinary017⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary018⟩,⟨evidence3Ordinary018⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary019⟩,⟨evidence3Ordinary019⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary020⟩,⟨evidence3Ordinary020⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary021⟩,⟨evidence3Ordinary021⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary022⟩,⟨evidence3Ordinary022⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary023⟩,⟨evidence3Ordinary023⟩⟩
  simp

end PiPolynomialValues.Certificates
