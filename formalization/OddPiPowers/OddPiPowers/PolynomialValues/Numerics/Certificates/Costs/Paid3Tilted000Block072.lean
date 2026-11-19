module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet3Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan3
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2004110253588034382240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2003722621249556341400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002459339011982894160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002431037205394905840000 := by decide +kernel

theorem paid3Tilted000Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=8012723251054968523640000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block072Slice072 paid3Tilted000Block072Slice075)) paid3Tilted000Block072Slice078)) paid3Tilted000Block072Slice081))

end PiPolynomialValues.Certificates
