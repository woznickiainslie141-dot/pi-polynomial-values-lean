module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted003Block000. -/
/- Independently checkable declarations from Paid2Tilted003Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269133197903579810200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269185039024439259280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269417729680055380880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269508540069880838160000 := by decide +kernel

theorem paid2Tilted003Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1077244506677955288520000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block000Slice000 paid2Tilted003Block000Slice003)) paid2Tilted003Block000Slice006)) paid2Tilted003Block000Slice009))
/- Independently checkable declarations from Paid2Tilted003Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269599313331387253920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269470835823998852440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270023014634151758720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270138413164859926400000 := by decide +kernel

theorem paid2Tilted003Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079231576954397791480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block012Slice012 paid2Tilted003Block012Slice015)) paid2Tilted003Block012Slice018)) paid2Tilted003Block012Slice021))
/- Independently checkable declarations from Paid2Tilted003Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270502285937402486480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270005373968147992280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784846584299124440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784602632135622600000 := by decide +kernel

theorem paid2Tilted003Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1080077109121985225800000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block024Slice024 paid2Tilted003Block024Slice027)) paid2Tilted003Block024Slice030)) paid2Tilted003Block024Slice033))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted003Block036. -/
/- Independently checkable declarations from Paid2Tilted003Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784391597946386320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784191745695069720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784053203872851560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783906898412048280000 := by decide +kernel

theorem paid2Tilted003Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079136543445926355880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block036Slice036 paid2Tilted003Block036Slice039)) paid2Tilted003Block036Slice042)) paid2Tilted003Block036Slice045))
/- Independently checkable declarations from Paid2Tilted003Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783781030402616640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783652888986441560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783558957899885160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783478543971101680000 := by decide +kernel

theorem paid2Tilted003Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079134471421260045040000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block048Slice048 paid2Tilted003Block048Slice051)) paid2Tilted003Block048Slice054)) paid2Tilted003Block048Slice057))
/- Independently checkable declarations from Paid2Tilted003Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783376814775246520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783376814775246520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783478543971101680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783558957899885160000 := by decide +kernel

theorem paid2Tilted003Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079133791131421479880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block060Slice060 paid2Tilted003Block060Slice063)) paid2Tilted003Block060Slice066)) paid2Tilted003Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted003Block072. -/
/- Independently checkable declarations from Paid2Tilted003Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783652888986441560000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783781030402616640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269783906898412048280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784053203872851560000 := by decide +kernel

theorem paid2Tilted003Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079135394021673958040000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block072Slice072 paid2Tilted003Block072Slice075)) paid2Tilted003Block072Slice078)) paid2Tilted003Block072Slice081))
/- Independently checkable declarations from Paid2Tilted003Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784191745695069720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784391597946386320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784602632135622600000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269784846584299124440000 := by decide +kernel

theorem paid2Tilted003Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1079138032560076203080000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block084Slice084 paid2Tilted003Block084Slice087)) paid2Tilted003Block084Slice090)) paid2Tilted003Block084Slice093))
/- Independently checkable declarations from Paid2Tilted003Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270005373968147992280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270502285937402486480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270138413164859926400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=270023014634151758720000 := by decide +kernel

theorem paid2Tilted003Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1080669087704562163880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block096Slice096 paid2Tilted003Block096Slice099)) paid2Tilted003Block096Slice102)) paid2Tilted003Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted003Block108. -/
/- Independently checkable declarations from Paid2Tilted003Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269470835823998852440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269599313331387253920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269508540069880838160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269417729680055380880000 := by decide +kernel

theorem paid2Tilted003Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=1077996418905322325400000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block108Slice108 paid2Tilted003Block108Slice111)) paid2Tilted003Block108Slice114)) paid2Tilted003Block108Slice117))
/- Independently checkable declarations from Paid2Tilted003Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted003Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=269185039024439259280000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted003Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=179422477827549762120000 := by decide +kernel

theorem paid2Tilted003Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=448607516851989021400000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block120Slice120 paid2Tilted003Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted003. -/
theorem trap2Tilted003 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted003 FourPeriod.quadraticShape.widths anchorPlan2 1598 r (spatialBasis r))=11239504448796569858400000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted003Block000 paid2Tilted003Block012)) paid2Tilted003Block024)) paid2Tilted003Block036)) paid2Tilted003Block048)) paid2Tilted003Block060)) paid2Tilted003Block072)) paid2Tilted003Block084)) paid2Tilted003Block096)) paid2Tilted003Block108)) paid2Tilted003Block120))

end PiPolynomialValues.Certificates
