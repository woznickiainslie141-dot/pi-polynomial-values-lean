module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted001Block036. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5209907389623365247880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5208353728745915338520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206795578464991968440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5206792371699690772240000 := by decide +kernel

theorem paid3Tilted001Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20831849068533963327080000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block036Slice036 paid3Tilted001Block036Slice039)) paid3Tilted001Block036Slice042)) paid3Tilted001Block036Slice045))
/- Independently checkable declarations from Paid3Tilted001Block048. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5209579493762773556000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210487324628690234960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210837800996146258160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210374503502851621880000 := by decide +kernel

theorem paid3Tilted001Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20841279122890461671000000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block048Slice048 paid3Tilted001Block048Slice051)) paid3Tilted001Block048Slice054)) paid3Tilted001Block048Slice057))
/- Independently checkable declarations from Paid3Tilted001Block060. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted001Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5211904336143957540520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5211904336143957540520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210374503502851621880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted001Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=5210837800996146258160000 := by decide +kernel

theorem paid3Tilted001Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=20845020976786912961080000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted001 FourPeriod.cubicShape.widths anchorPlan3 20119 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted001Block060Slice060 paid3Tilted001Block060Slice063)) paid3Tilted001Block060Slice066)) paid3Tilted001Block060Slice069))

end PiPolynomialValues.Certificates
