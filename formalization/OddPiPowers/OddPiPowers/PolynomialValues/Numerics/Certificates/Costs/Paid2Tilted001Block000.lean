module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Independently checkable declarations from Paid2Tilted001Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487322403624097184880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487365976733186889760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487677224303280121240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487812350442622984320000 := by decide +kernel

theorem paid2Tilted001Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1950177955103187180200000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block000Slice000 paid2Tilted001Block000Slice003)) paid2Tilted001Block000Slice006)) paid2Tilted001Block000Slice009))
/- Independently checkable declarations from Paid2Tilted001Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487947444502474481920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=487752319148932296200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488476454027537200720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488628572711769514880000 := by decide +kernel

theorem paid2Tilted001Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1952804790390713493720000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block012Slice012 paid2Tilted001Block012Slice015)) paid2Tilted001Block012Slice018)) paid2Tilted001Block012Slice021))
/- Independently checkable declarations from Paid2Tilted001Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted001Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=489136679304752281760000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488445024972453227240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488133526910703175360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted001Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=488133131840422730720000 := by decide +kernel

theorem paid2Tilted001Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=1953848363028331415080000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted001 FourPeriod.quadraticShape.widths anchorPlan2 4107 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted001Block024Slice024 paid2Tilted001Block024Slice027)) paid2Tilted001Block024Slice030)) paid2Tilted001Block024Slice033))

end PiPolynomialValues.Certificates
