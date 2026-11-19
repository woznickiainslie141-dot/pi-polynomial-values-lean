module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted001Block072. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210487324628690234960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5209579493762773556000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206792371699690772240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206795578464991968440000 := by decide +kernel

theorem paid3Tilted001Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20833654768556146531640000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block072Slice072 paid3Tilted001Block072Slice075)) paid3Tilted001Block072Slice078)) paid3Tilted001Block072Slice081))
/- Independently checkable declarations from Paid3Tilted001Block084. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5208353728745915338520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5209907389623365247880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206927097335624383000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206407711729124812240000 := by decide +kernel

theorem paid3Tilted001Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20831595927434029781640000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block084Slice084 paid3Tilted001Block084Slice087)) paid3Tilted001Block084Slice090)) paid3Tilted001Block084Slice093))
/- Independently checkable declarations from Paid3Tilted001Block096. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206676383503787011600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5205125063983962212800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203690851755385002560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5203691625535536040400000 := by decide +kernel

theorem paid3Tilted001Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20819183924778670267360000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block096Slice096 paid3Tilted001Block096Slice099)) paid3Tilted001Block096Slice102)) paid3Tilted001Block096Slice105))

end PiPolynomialValues.Certificates
