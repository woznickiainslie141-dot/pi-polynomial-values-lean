module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted001Block000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted001Block036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted001Block072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted001Block108

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Tilted001 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=216962760094665335523120000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block000 paid3Tilted001Block012)) paid3Tilted001Block024)) paid3Tilted001Block036)) paid3Tilted001Block048)) paid3Tilted001Block060)) paid3Tilted001Block072)) paid3Tilted001Block084)) paid3Tilted001Block096)) paid3Tilted001Block108)) paid3Tilted001Block120))

end PiPolynomialValues.Certificates
