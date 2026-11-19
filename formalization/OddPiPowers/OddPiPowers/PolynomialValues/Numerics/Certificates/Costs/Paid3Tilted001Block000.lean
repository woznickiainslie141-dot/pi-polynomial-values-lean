module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted001Block000. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5208423066560766763800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206428904040431600440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204713996168621835640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204245615505650912200000 := by decide +kernel

theorem paid3Tilted001Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20823811582275471112080000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block000Slice000 paid3Tilted001Block000Slice003)) paid3Tilted001Block000Slice006)) paid3Tilted001Block000Slice009))
/- Independently checkable declarations from Paid3Tilted001Block012. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5204393991483356668760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203693761791401279840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203691625535536040400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203690851755385002560000 := by decide +kernel

theorem paid3Tilted001Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20815470230565678991560000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block012Slice012 paid3Tilted001Block012Slice015)) paid3Tilted001Block012Slice018)) paid3Tilted001Block012Slice021))
/- Independently checkable declarations from Paid3Tilted001Block024. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5205125063983962212800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206676383503787011600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206407711729124812240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206927097335624383000000 := by decide +kernel

theorem paid3Tilted001Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20825136256552498419640000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block024Slice024 paid3Tilted001Block024Slice027)) paid3Tilted001Block024Slice030)) paid3Tilted001Block024Slice033))

end PiPolynomialValues.Certificates
