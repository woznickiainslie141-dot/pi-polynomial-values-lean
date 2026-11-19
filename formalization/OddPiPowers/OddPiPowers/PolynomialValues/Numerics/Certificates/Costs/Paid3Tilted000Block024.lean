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
theorem paid3Tilted000Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2001642315729733573720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002312596816627761680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002203128305063857600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid3Tilted000Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=2002447913226875081000000 := by decide +kernel

theorem paid3Tilted000Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=8008605954078300274000000 := by
  rw [show (fun r => quickReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r))=(fun r => anchorReferenceCost reference3Tilted000 FourPeriod.cubicShape.widths anchorPlan3 151 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan3_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid3Tilted000Block024Slice024 paid3Tilted000Block024Slice027)) paid3Tilted000Block024Slice030)) paid3Tilted000Block024Slice033))

end PiPolynomialValues.Certificates
