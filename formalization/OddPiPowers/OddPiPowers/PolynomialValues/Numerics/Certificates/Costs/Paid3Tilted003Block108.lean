module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted003Block108. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293775104625341775560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294359707688945054960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294238539045900917440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294615344622327378920000 := by decide +kernel

theorem paid3Tilted003Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17176988695982515126880000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block108Slice108 paid3Tilted003Block108Slice111)) paid3Tilted003Block108Slice114)) paid3Tilted003Block108Slice117))
/- Independently checkable declarations from Paid3Tilted003Block120. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296027468161033730440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=2865118958888054110920000 := by decide +kernel

theorem paid3Tilted003Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=7161146427049087841360000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block120Slice120 paid3Tilted003Block120Slice123))

end PiPolynomialValues.Certificates
