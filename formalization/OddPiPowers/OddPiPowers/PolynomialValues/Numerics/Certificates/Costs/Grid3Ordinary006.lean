module

public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Ordinary006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Grid3Ordinary006. -/
set_option maxRecDepth 8192 in
theorem trap3Ordinary006Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1493147491717474547360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary006Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1492798985257590603280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary006Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1492402516416189766080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary006Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1492766146183181697400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary006Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-1493152934547769301240000 := by decide +kernel

theorem trap3Ordinary006 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary006 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=-7464268074122205915360000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary006Part000 trap3Ordinary006Part025)) trap3Ordinary006Part050)) trap3Ordinary006Part075)) trap3Ordinary006Part100))
/- Independently checkable declarations from Grid3Ordinary007. -/
set_option maxRecDepth 8192 in
theorem trap3Ordinary007Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=43372312900558561719840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary007Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=43393893968615534216600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary007Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=43422547222409989087520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary007Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=43395566232623664074640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary007Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=43371221842859255885640000 := by decide +kernel

theorem trap3Ordinary007 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary007 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=216955542167067004984240000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary007Part000 trap3Ordinary007Part025)) trap3Ordinary007Part050)) trap3Ordinary007Part075)) trap3Ordinary007Part100))
/- Independently checkable declarations from Grid3Ordinary008. -/
set_option maxRecDepth 8192 in
theorem trap3Ordinary008Part000 : gridCostBlock 0 25 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=3176222406216650868920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary008Part025 : gridCostBlock 25 25 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=3179895522528732103760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary008Part050 : gridCostBlock 50 25 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=3184653103491231416000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary008Part075 : gridCostBlock 75 25 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=3180191396429189800280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem trap3Ordinary008Part100 : gridCostBlock 100 25 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=3176059788049135876160000 := by decide +kernel

theorem trap3Ordinary008 : gridCostBlock 0 125 (fun r => quickReferenceCost reference3Ordinary008 FourPeriod.cubicShape.widths anchorPlan3 0 r (spatialBasis r))=15897022216714940065120000 :=
  ((gridCostBlock_join 0 100 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 75 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 50 25 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 25 25 _).symm.trans (congrArg₂ (·+·) trap3Ordinary008Part000 trap3Ordinary008Part025)) trap3Ordinary008Part050)) trap3Ordinary008Part075)) trap3Ordinary008Part100))

end PiPolynomialValues.Certificates
