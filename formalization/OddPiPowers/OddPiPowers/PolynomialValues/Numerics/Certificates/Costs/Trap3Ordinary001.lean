module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001Part000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001Part025
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001Part050
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001Part075
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap3Ordinary001Part100

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Ordinary001 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary001 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-5806291944609630912080000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary001Part000 trap3Ordinary001Part025)) trap3Ordinary001Part050)) trap3Ordinary001Part075)) trap3Ordinary001Part100))

end PiPolynomialValues.Certificates
