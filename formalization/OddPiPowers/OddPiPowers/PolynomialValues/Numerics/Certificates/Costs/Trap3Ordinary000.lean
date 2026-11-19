module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary000Part000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary000Part025

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Ordinary000 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary000 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-5671210277818764078800000 :=
  ((gridCostBlock_join 0 25 100 _).symm.trans (congrArg₂ (·+·) trap3Ordinary000Part000 trap3Ordinary000Part025))

end PiPolynomialValues.Certificates
