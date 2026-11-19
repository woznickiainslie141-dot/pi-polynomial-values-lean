module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted003Block036. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4298832003696071829600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4297564525068694387400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296297265395702249920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296298685316984208320000 := by decide +kernel

theorem paid3Tilted003Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17188992479477452675240000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block036Slice036 paid3Tilted003Block036Slice039)) paid3Tilted003Block036Slice042)) paid3Tilted003Block036Slice045))
/- Independently checkable declarations from Paid3Tilted003Block048. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4298567485386848222280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299317684407709510000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299614243427494929120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299224022615971002200000 := by decide +kernel

theorem paid3Tilted003Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17196723435838023663600000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block048Slice048 paid3Tilted003Block048Slice051)) paid3Tilted003Block048Slice054)) paid3Tilted003Block048Slice057))
/- Independently checkable declarations from Paid3Tilted003Block060. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4300503636536231689880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4300503636536231689880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299224022615971002200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299614243427494929120000 := by decide +kernel

theorem paid3Tilted003Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17199845539115929311080000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block060Slice060 paid3Tilted003Block060Slice063)) paid3Tilted003Block060Slice066)) paid3Tilted003Block060Slice069))

end PiPolynomialValues.Certificates
