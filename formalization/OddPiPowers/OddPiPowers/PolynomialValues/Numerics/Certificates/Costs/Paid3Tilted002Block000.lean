module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted002Block000. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987996964098893337520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986763353347947107400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985706066284141464840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985415852324343802880000 := by decide +kernel

theorem paid3Tilted002Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11945882236055325712640000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block000Slice000 paid3Tilted002Block000Slice003)) paid3Tilted002Block000Slice006)) paid3Tilted002Block000Slice009))
/- Independently checkable declarations from Paid3Tilted002Block012. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985511154853330269480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085603568624726840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085401610328330320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085939171963713040000 := by decide +kernel

theorem paid3Tilted002Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11940768099204247039680000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block012Slice012 paid3Tilted002Block012Slice015)) paid3Tilted002Block012Slice018)) paid3Tilted002Block012Slice021))
/- Independently checkable declarations from Paid3Tilted002Block024. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985968626009742243720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986903104229002814320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986744966121072799040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987069493143485517680000 := by decide +kernel

theorem paid3Tilted002Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11946686189503303374760000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block024Slice024 paid3Tilted002Block024Slice027)) paid3Tilted002Block024Slice030)) paid3Tilted002Block024Slice033))

end PiPolynomialValues.Certificates
