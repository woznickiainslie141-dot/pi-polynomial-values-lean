module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2000995145266318091440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2001293232926251224480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2001221833861546374960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2001440851143684405240000 := by decide +kernel

theorem paid3Tilted000Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=8004951063197800096120000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block108Slice108 paid3Tilted000Block108Slice111)) paid3Tilted000Block108Slice114)) paid3Tilted000Block108Slice117))

end PiPolynomialValues.Certificates
