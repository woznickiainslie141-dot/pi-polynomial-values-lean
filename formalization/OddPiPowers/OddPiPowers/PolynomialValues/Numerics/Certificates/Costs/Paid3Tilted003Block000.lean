module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted003Block000. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4297678491375347574120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296027468161033730440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294615344622327378920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294238539045900917440000 := by decide +kernel

theorem paid3Tilted003Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17182559843204609600920000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block000Slice000 paid3Tilted003Block000Slice003)) paid3Tilted003Block000Slice006)) paid3Tilted003Block000Slice009))
/- Independently checkable declarations from Paid3Tilted003Block012. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294359707688945054960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293775104625341775560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293773723621297952120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293773670386951285800000 := by decide +kernel

theorem paid3Tilted003Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17175682206322536068440000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block012Slice012 paid3Tilted003Block012Slice015)) paid3Tilted003Block012Slice018)) paid3Tilted003Block012Slice021))
/- Independently checkable declarations from Paid3Tilted003Block024. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294948778316184992000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296222440139316584520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4295992288991096053160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296411227023299363800000 := by decide +kernel

theorem paid3Tilted003Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17183574734469896993480000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block024Slice024 paid3Tilted003Block024Slice027)) paid3Tilted003Block024Slice030)) paid3Tilted003Block024Slice033))

end PiPolynomialValues.Certificates
