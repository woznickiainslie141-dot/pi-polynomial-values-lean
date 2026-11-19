module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary000Part000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary000Part005
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary000Part045
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Trap2Ordinary000Part085

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap2Ordinary000 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Ordinary000 FourPeriod.quadraticShape.widths anchorPlan2 0 r (spatialBasis r))=-3515078167381754909360000 :=
  ((gridCostBlock_join 0 85 40 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 45 40 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 5 40 _).symm.trans (congrArg₂ (·+·) trap2Ordinary000Part000 trap2Ordinary000Part005)) trap2Ordinary000Part045)) trap2Ordinary000Part085))

end PiPolynomialValues.Certificates
