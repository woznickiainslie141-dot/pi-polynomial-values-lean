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
theorem paid3Tilted000Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2003103949088297772720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2003804626485344467120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002447913226875081000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002203128305063857600000 := by decide +kernel

theorem paid3Tilted000Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=8011559617105581178440000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block084Slice084 paid3Tilted000Block084Slice087)) paid3Tilted000Block084Slice090)) paid3Tilted000Block084Slice093))

end PiPolynomialValues.Certificates
