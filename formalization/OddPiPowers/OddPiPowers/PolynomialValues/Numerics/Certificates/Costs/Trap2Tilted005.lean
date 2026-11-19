module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted005Block000. -/
/- Independently checkable declarations from Paid2Tilted005Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=694982657464579697040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695014827445756242560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695389361431336224240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695568546329947440160000 := by decide +kernel

theorem paid2Tilted005Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2780955392671619604000000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block000Slice000 paid2Tilted005Block000Slice003)) paid2Tilted005Block000Slice006)) paid2Tilted005Block000Slice009))
/- Independently checkable declarations from Paid2Tilted005Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695747552416733323280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695484991534704594200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696347458609736290120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696529765422405824920000 := by decide +kernel

theorem paid2Tilted005Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2784109767983580032520000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block012Slice012 paid2Tilted005Block012Slice015)) paid2Tilted005Block012Slice018)) paid2Tilted005Block012Slice021))
/- Independently checkable declarations from Paid2Tilted005Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=697162011054185098800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696301330764026617040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695907154494635530560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695906512394604535040000 := by decide +kernel

theorem paid2Tilted005Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2785277008707451781440000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block024Slice024 paid2Tilted005Block024Slice027)) paid2Tilted005Block024Slice030)) paid2Tilted005Block024Slice033))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted005Block036. -/
/- Independently checkable declarations from Paid2Tilted005Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905938859229548320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905398096433287640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905210735661671880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904955150690294040000 := by decide +kernel

theorem paid2Tilted005Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2783621502842014801880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block036Slice036 paid2Tilted005Block036Slice039)) paid2Tilted005Block036Slice042)) paid2Tilted005Block036Slice045))
/- Independently checkable declarations from Paid2Tilted005Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904646950966387680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904251233953427080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903953073013214320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903715056058547600000 := by decide +kernel

theorem paid2Tilted005Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2783616566313991576680000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block048Slice048 paid2Tilted005Block048Slice051)) paid2Tilted005Block048Slice054)) paid2Tilted005Block048Slice057))
/- Independently checkable declarations from Paid2Tilted005Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903413787470964000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903413787470964000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903715056058547600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695903953073013214320000 := by decide +kernel

theorem paid2Tilted005Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2783614495704013689920000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block060Slice060 paid2Tilted005Block060Slice063)) paid2Tilted005Block060Slice066)) paid2Tilted005Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted005Block072. -/
/- Independently checkable declarations from Paid2Tilted005Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904251233953427080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904646950966387680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695904955150690294040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905210735661671880000 := by decide +kernel

theorem paid2Tilted005Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2783619064071271780680000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block072Slice072 paid2Tilted005Block072Slice075)) paid2Tilted005Block072Slice078)) paid2Tilted005Block072Slice081))
/- Independently checkable declarations from Paid2Tilted005Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905398096433287640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695905938859229548320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695906512394604535040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695907154494635530560000 := by decide +kernel

theorem paid2Tilted005Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2783625003844902901560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block084Slice084 paid2Tilted005Block084Slice087)) paid2Tilted005Block084Slice090)) paid2Tilted005Block084Slice093))
/- Independently checkable declarations from Paid2Tilted005Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696301330764026617040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=697162011054185098800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696529765422405824920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=696347458609736290120000 := by decide +kernel

theorem paid2Tilted005Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2786340565850353830880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block096Slice096 paid2Tilted005Block096Slice099)) paid2Tilted005Block096Slice102)) paid2Tilted005Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted005Block108. -/
/- Independently checkable declarations from Paid2Tilted005Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695484991534704594200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695747552416733323280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695568546329947440160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695389361431336224240000 := by decide +kernel

theorem paid2Tilted005Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=2782190451712721581880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block108Slice108 paid2Tilted005Block108Slice111)) paid2Tilted005Block108Slice114)) paid2Tilted005Block108Slice117))
/- Independently checkable declarations from Paid2Tilted005Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted005Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=695014827445756242560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted005Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=463318917319320246640000 := by decide +kernel

theorem paid2Tilted005Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=1158333744765076489200000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block120Slice120 paid2Tilted005Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted005. -/
theorem trap2Tilted005 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted005 FourPeriod.quadraticShape.widths anchorPlan2 5787 r (spatialBasis r))=28995303564466998070640000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted005Block000 paid2Tilted005Block012)) paid2Tilted005Block024)) paid2Tilted005Block036)) paid2Tilted005Block048)) paid2Tilted005Block060)) paid2Tilted005Block072)) paid2Tilted005Block084)) paid2Tilted005Block096)) paid2Tilted005Block108)) paid2Tilted005Block120))

end PiPolynomialValues.Certificates
