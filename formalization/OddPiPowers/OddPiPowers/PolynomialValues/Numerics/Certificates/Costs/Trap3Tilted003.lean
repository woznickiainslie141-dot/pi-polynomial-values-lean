module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted003Block000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted003Block036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted003Block072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted003Block108

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Tilted003 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=179023513139210207919920000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block000 paid3Tilted003Block012)) paid3Tilted003Block024)) paid3Tilted003Block036)) paid3Tilted003Block048)) paid3Tilted003Block060)) paid3Tilted003Block072)) paid3Tilted003Block084)) paid3Tilted003Block096)) paid3Tilted003Block108)) paid3Tilted003Block120))

end PiPolynomialValues.Certificates
