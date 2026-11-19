module

public import OddPiPowers.PolynomialValues.Numerics.LabelReferences
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AngleDesign3
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary084
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary087
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Batch3Ordinary090

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem angleLabels3_084_references : ∀ t∈angleLabels3_084, LabelReferencePair FourPeriod.cubicShape anchorPlan3 t := by
  apply labelPairs_cons ⟨⟨evidence3Ordinary084⟩,⟨evidence3Ordinary084⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary085⟩,⟨evidence3Ordinary085⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary086⟩,⟨evidence3Ordinary086⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary087⟩,⟨evidence3Ordinary087⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary088⟩,⟨evidence3Ordinary088⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary089⟩,⟨evidence3Ordinary089⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary090⟩,⟨evidence3Ordinary090⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary091⟩,⟨evidence3Ordinary091⟩⟩
  apply labelPairs_cons ⟨⟨evidence3Ordinary092⟩,⟨evidence3Ordinary092⟩⟩
  simp

end PiPolynomialValues.Certificates
