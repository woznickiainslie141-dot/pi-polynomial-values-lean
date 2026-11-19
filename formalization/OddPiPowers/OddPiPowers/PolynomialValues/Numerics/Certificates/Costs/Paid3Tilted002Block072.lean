module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted002Block072. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989285630967406213280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2988741462421448377880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987030888952736757120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987011015482481535920000 := by decide +kernel

theorem paid3Tilted002Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11952068997824072884200000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block072Slice072 paid3Tilted002Block072Slice075)) paid3Tilted002Block072Slice078)) paid3Tilted002Block072Slice081))
/- Independently checkable declarations from Paid3Tilted002Block084. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987945375418627183240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2988898860141082051040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987069493143485517680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986744966121072799040000 := by decide +kernel

theorem paid3Tilted002Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11950658694824267551000000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block084Slice084 paid3Tilted002Block084Slice087)) paid3Tilted002Block084Slice090)) paid3Tilted002Block084Slice093))
/- Independently checkable declarations from Paid3Tilted002Block096. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2986903104229002814320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985968626009742243720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085939171963713040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2985085401610328330320000 := by decide +kernel

theorem paid3Tilted002Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11943043071021037101400000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block096Slice096 paid3Tilted002Block096Slice099)) paid3Tilted002Block096Slice102)) paid3Tilted002Block096Slice105))

end PiPolynomialValues.Certificates
