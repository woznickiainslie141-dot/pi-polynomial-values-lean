module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block012
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block024
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block036
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block048
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block060
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block084
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block096
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block108
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid3Tilted000Block120

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap3Tilted000 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=83439293116663881787440000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block000 paid3Tilted000Block012)) paid3Tilted000Block024)) paid3Tilted000Block036)) paid3Tilted000Block048)) paid3Tilted000Block060)) paid3Tilted000Block072)) paid3Tilted000Block084)) paid3Tilted000Block096)) paid3Tilted000Block108)) paid3Tilted000Block120))

end PiPolynomialValues.Certificates
