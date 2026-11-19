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
theorem paid3Tilted000Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2003804626485344467120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2003103949088297772720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002431037205394905840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002459339011982894160000 := by decide +kernel

theorem paid3Tilted000Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=8011798951791020039840000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block036Slice036 paid3Tilted000Block036Slice039)) paid3Tilted000Block036Slice042)) paid3Tilted000Block036Slice045))

end PiPolynomialValues.Certificates
