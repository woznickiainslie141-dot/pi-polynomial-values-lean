module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted003Block072. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4299317684407709510000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4298567485386848222280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296298685316984208320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296297265395702249920000 := by decide +kernel

theorem paid3Tilted003Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17190481120507244190520000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block072Slice072 paid3Tilted003Block072Slice075)) paid3Tilted003Block072Slice078)) paid3Tilted003Block072Slice081))
/- Independently checkable declarations from Paid3Tilted003Block084. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4297564525068694387400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4298832003696071829600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296411227023299363800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4295992288991096053160000 := by decide +kernel

theorem paid3Tilted003Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17188800044779161633960000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block084Slice084 paid3Tilted003Block084Slice087)) paid3Tilted003Block084Slice090)) paid3Tilted003Block084Slice093))
/- Independently checkable declarations from Paid3Tilted003Block096. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted003Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4296222440139316584520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4294948778316184992000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293773670386951285800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted003Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=4293773723621297952120000 := by decide +kernel

theorem paid3Tilted003Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=17178718612463750814440000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted003 FourPeriod.cubicShape.widths anchorPlan3 11676 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted003Block096Slice096 paid3Tilted003Block096Slice099)) paid3Tilted003Block096Slice102)) paid3Tilted003Block096Slice105))

end PiPolynomialValues.Certificates
