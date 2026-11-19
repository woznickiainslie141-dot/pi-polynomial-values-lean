module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block015
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block027
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block039
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block051
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block063
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block075
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block087
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block099
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block111
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Costs.Paid2Tilted000Block123

@[expose] public section

namespace PiPolynomialValues.Certificates

theorem trap2Tilted000Part003 : gridCostBlock 3 122 (fun r => quickReferenceCost reference2Tilted000 FourPeriod.quadraticShape.widths anchorPlan2 1321 r (spatialBasis r))=10022752143568665225920000 :=
  ((gridCostBlock_join 3 120 2 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 3 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted000Block003 paid2Tilted000Block015)) paid2Tilted000Block027)) paid2Tilted000Block039)) paid2Tilted000Block051)) paid2Tilted000Block063)) paid2Tilted000Block075)) paid2Tilted000Block087)) paid2Tilted000Block099)) paid2Tilted000Block111)) paid2Tilted000Block123))

end PiPolynomialValues.Certificates
