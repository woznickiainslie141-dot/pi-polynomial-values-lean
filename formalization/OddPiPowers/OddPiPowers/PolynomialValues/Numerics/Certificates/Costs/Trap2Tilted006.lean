module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted006
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted006Block000. -/
/- Independently checkable declarations from Paid2Tilted006Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360516060603025575080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360563431828331394400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360827273836450306200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360936856675353088480000 := by decide +kernel

theorem paid2Tilted006Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1442843622943160364160000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block000Slice000 paid2Tilted006Block000Slice003)) paid2Tilted006Block000Slice006)) paid2Tilted006Block000Slice009))
/- Independently checkable declarations from Paid2Tilted006Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361046427476126280880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360889413500909483920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361511390023491855360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361641716270872992880000 := by decide +kernel

theorem paid2Tilted006Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1445088947271400613040000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block012Slice012 paid2Tilted006Block012Slice015)) paid2Tilted006Block012Slice018)) paid2Tilted006Block012Slice021))
/- Independently checkable declarations from Paid2Tilted006Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=362064729999698350880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361487642379353949080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361229238580533952480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228834467679102840000 := by decide +kernel

theorem paid2Tilted006Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1446010445427265355280000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block024Slice024 paid2Tilted006Block024Slice027)) paid2Tilted006Block024Slice030)) paid2Tilted006Block024Slice033))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted006Block036. -/
/- Independently checkable declarations from Paid2Tilted006Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228499516901609120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228186063743004520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227979739631097600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227784921125744200000 := by decide +kernel

theorem paid2Tilted006Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1444912450241401455440000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block036Slice036 paid2Tilted006Block036Slice039)) paid2Tilted006Block036Slice042)) paid2Tilted006Block036Slice045))
/- Independently checkable declarations from Paid2Tilted006Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227626931822751280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227435948086479040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227306315725108880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227186839665670960000 := by decide +kernel

theorem paid2Tilted006Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1444909556035300010160000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block048Slice048 paid2Tilted006Block048Slice051)) paid2Tilted006Block048Slice054)) paid2Tilted006Block048Slice057))
/- Independently checkable declarations from Paid2Tilted006Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227073190952690360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227073190952690360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227186839665670960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227306315725108880000 := by decide +kernel

theorem paid2Tilted006Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1444908639537296160560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block060Slice060 paid2Tilted006Block060Slice063)) paid2Tilted006Block060Slice066)) paid2Tilted006Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted006Block072. -/
/- Independently checkable declarations from Paid2Tilted006Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227435948086479040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227626931822751280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227784921125744200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361227979739631097600000 := by decide +kernel

theorem paid2Tilted006Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1444910827540666072120000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block072Slice072 paid2Tilted006Block072Slice075)) paid2Tilted006Block072Slice078)) paid2Tilted006Block072Slice081))
/- Independently checkable declarations from Paid2Tilted006Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228186063743004520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228499516901609120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361228834467679102840000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361229238580533952480000 := by decide +kernel

theorem paid2Tilted006Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1444914758628857668960000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block084Slice084 paid2Tilted006Block084Slice087)) paid2Tilted006Block084Slice090)) paid2Tilted006Block084Slice093))
/- Independently checkable declarations from Paid2Tilted006Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361487642379353949080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=362064729999698350880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361641716270872992880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361511390023491855360000 := by decide +kernel

theorem paid2Tilted006Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1446705478673417148200000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block096Slice096 paid2Tilted006Block096Slice099)) paid2Tilted006Block096Slice102)) paid2Tilted006Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted006Block108. -/
/- Independently checkable declarations from Paid2Tilted006Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360889413500909483920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=361046427476126280880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360936856675353088480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360827273836450306200000 := by decide +kernel

theorem paid2Tilted006Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=1443699971488839159480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block108Slice108 paid2Tilted006Block108Slice111)) paid2Tilted006Block108Slice114)) paid2Tilted006Block108Slice117))
/- Independently checkable declarations from Paid2Tilted006Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted006Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=360563431828331394400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted006Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=240343675619880575880000 := by decide +kernel

theorem paid2Tilted006Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=600907107448211970280000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block120Slice120 paid2Tilted006Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted006. -/
theorem trap2Tilted006 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted006 FourPeriod.quadraticShape.widths anchorPlan2 2650 r (spatialBasis r))=15049811805235815977680000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted006Block000 paid2Tilted006Block012)) paid2Tilted006Block024)) paid2Tilted006Block036)) paid2Tilted006Block048)) paid2Tilted006Block060)) paid2Tilted006Block072)) paid2Tilted006Block084)) paid2Tilted006Block096)) paid2Tilted006Block108)) paid2Tilted006Block120))

end PiPolynomialValues.Certificates
