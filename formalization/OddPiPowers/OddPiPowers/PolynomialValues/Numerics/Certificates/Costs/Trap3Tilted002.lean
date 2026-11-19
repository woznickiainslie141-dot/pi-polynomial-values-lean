module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted002Block000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted002Block036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted002Block072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted002Block108

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Tilted002 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=124466189150135732464080000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block000 paid3Tilted002Block012)) paid3Tilted002Block024)) paid3Tilted002Block036)) paid3Tilted002Block048)) paid3Tilted002Block060)) paid3Tilted002Block072)) paid3Tilted002Block084)) paid3Tilted002Block096)) paid3Tilted002Block108)) paid3Tilted002Block120))

end PiPolynomialValues.Certificates
