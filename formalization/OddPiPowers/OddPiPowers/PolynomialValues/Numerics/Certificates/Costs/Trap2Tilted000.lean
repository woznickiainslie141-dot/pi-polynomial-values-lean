module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted000Part000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Tilted000Part003

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap2Tilted000 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=10268608088935730619600000 :=
  ((gridCostBlock_join 0 3 122 _).symm.trans (congrArg₂ (·+·) trap2Tilted000Part000 trap2Tilted000Part003))

end PiPolynomialValues.Certificates
