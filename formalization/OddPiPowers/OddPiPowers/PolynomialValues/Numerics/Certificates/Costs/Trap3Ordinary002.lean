module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002Part000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002Part025
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002Part050
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002Part075
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary002Part100

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Ordinary002 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary002 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=30651583118420817163840000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary002Part000 trap3Ordinary002Part025)) trap3Ordinary002Part050)) trap3Ordinary002Part075)) trap3Ordinary002Part100))

end PiPolynomialValues.Certificates
