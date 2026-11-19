module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted001Block108. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203693761791401279840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204393991483356668760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204245615505650912200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204713996168621835640000 := by decide +kernel

theorem paid3Tilted001Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20817047364949030696440000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block108Slice108 paid3Tilted001Block108Slice111)) paid3Tilted001Block108Slice114)) paid3Tilted001Block108Slice117))
/- Independently checkable declarations from Paid3Tilted001Block120. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206428904040431600440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=3472281967302040163160000 := by decide +kernel

theorem paid3Tilted001Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=8678710871342471763600000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block120Slice120 paid3Tilted001Block120Slice123))

end PiPolynomialValues.Certificates
