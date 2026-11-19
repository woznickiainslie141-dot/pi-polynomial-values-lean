module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid3Tilted002Block036. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2988898860141082051040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987945375418627183240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987011015482481535920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2987030888952736757120000 := by decide +kernel

theorem paid3Tilted002Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11950886139994927527320000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block036Slice036 paid3Tilted002Block036Slice039)) paid3Tilted002Block036Slice042)) paid3Tilted002Block036Slice045))
/- Independently checkable declarations from Paid3Tilted002Block048. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2988741462421448377880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989285630967406213280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989487789816004653600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989212847064896041040000 := by decide +kernel

theorem paid3Tilted002Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11956727730269755285800000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block048Slice048 paid3Tilted002Block048Slice051)) paid3Tilted002Block048Slice054)) paid3Tilted002Block048Slice057))
/- Independently checkable declarations from Paid3Tilted002Block060. -/
set_option maxRecDepth 8192 in
theorem paid3Tilted002Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2990143676936973613280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2990143676936973613280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989212847064896041040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted002Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=2989487789816004653600000 := by decide +kernel

theorem paid3Tilted002Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=11958987990754847921200000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted002 FourPeriod.cubicShape.widths anchorPlan3 4447 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted002Block060Slice060 paid3Tilted002Block060Slice063)) paid3Tilted002Block060Slice066)) paid3Tilted002Block060Slice069))

end PiPolynomialValues.Certificates
