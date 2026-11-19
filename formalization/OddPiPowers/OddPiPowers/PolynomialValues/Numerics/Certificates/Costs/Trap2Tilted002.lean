module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted002Block000. -/
/- Independently checkable declarations from Paid2Tilted002Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142069158613952261440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142124212869470501520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142308027827212498360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142372024805922556960000 := by decide +kernel

theorem paid2Tilted002Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=568873424116557818280000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block000Slice000 paid2Tilted002Block000Slice003)) paid2Tilted002Block000Slice006)) paid2Tilted002Block000Slice009))
/- Independently checkable declarations from Paid2Tilted002Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142436019142775973720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142347918603075134680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142791785271064841440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142884039883230454880000 := by decide +kernel

theorem paid2Tilted002Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570459762900146404720000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block012Slice012 paid2Tilted002Block012Slice015)) paid2Tilted002Block012Slice018)) paid2Tilted002Block012Slice021))
/- Independently checkable declarations from Paid2Tilted002Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=143159549080896335160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142782312693641393640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617615240958258000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617469674521766320000 := by decide +kernel

theorem paid2Tilted002Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=571176946690017753120000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block024Slice024 paid2Tilted002Block024Slice027)) paid2Tilted002Block024Slice030)) paid2Tilted002Block024Slice033))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted002Block036. -/
/- Independently checkable declarations from Paid2Tilted002Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617347954791533040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617226576168177120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617151771953416160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617075241916089680000 := by decide +kernel

theorem paid2Tilted002Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570468801544829216000000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block036Slice036 paid2Tilted002Block036Slice039)) paid2Tilted002Block036Slice042)) paid2Tilted002Block036Slice045))
/- Independently checkable declarations from Paid2Tilted002Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617027452296790640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616980912117076080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616964500155624480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616949451597550240000 := by decide +kernel

theorem paid2Tilted002Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570467922316167041440000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block048Slice048 paid2Tilted002Block048Slice051)) paid2Tilted002Block048Slice054)) paid2Tilted002Block048Slice057))
/- Independently checkable declarations from Paid2Tilted002Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616937387027159920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616937387027159920000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616949451597550240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616964500155624480000 := by decide +kernel

theorem paid2Tilted002Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570467788725807494560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block060Slice060 paid2Tilted002Block060Slice063)) paid2Tilted002Block060Slice066)) paid2Tilted002Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted002Block072. -/
/- Independently checkable declarations from Paid2Tilted002Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142616980912117076080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617027452296790640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617075241916089680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617151771953416160000 := by decide +kernel

theorem paid2Tilted002Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570468235378283372560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block072Slice072 paid2Tilted002Block072Slice075)) paid2Tilted002Block072Slice078)) paid2Tilted002Block072Slice081))
/- Independently checkable declarations from Paid2Tilted002Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617226576168177120000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617347954791533040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617469674521766320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142617615240958258000000 := by decide +kernel

theorem paid2Tilted002Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=570469659446439734480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block084Slice084 paid2Tilted002Block084Slice087)) paid2Tilted002Block084Slice090)) paid2Tilted002Block084Slice093))
/- Independently checkable declarations from Paid2Tilted002Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142782312693641393640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=143159549080896335160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142884039883230454880000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142791785271064841440000 := by decide +kernel

theorem paid2Tilted002Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=571617686928833025120000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block096Slice096 paid2Tilted002Block096Slice099)) paid2Tilted002Block096Slice102)) paid2Tilted002Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted002Block108. -/
/- Independently checkable declarations from Paid2Tilted002Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142347918603075134680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142436019142775973720000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142372024805922556960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142308027827212498360000 := by decide +kernel

theorem paid2Tilted002Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=569463990378986163720000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block108Slice108 paid2Tilted002Block108Slice111)) paid2Tilted002Block108Slice114)) paid2Tilted002Block108Slice117))
/- Independently checkable declarations from Paid2Tilted002Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted002Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=142124212869470501520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted002Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=94713988518381465840000 := by decide +kernel

theorem paid2Tilted002Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=236838201387851967360000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block120Slice120 paid2Tilted002Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted002. -/
theorem trap2Tilted002 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted002 FourPeriod.quadraticShape.widths anchorPlan2 350 r (spatialBasis r))=5940772419813919991360000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted002Block000 paid2Tilted002Block012)) paid2Tilted002Block024)) paid2Tilted002Block036)) paid2Tilted002Block048)) paid2Tilted002Block060)) paid2Tilted002Block072)) paid2Tilted002Block084)) paid2Tilted002Block096)) paid2Tilted002Block108)) paid2Tilted002Block120))

end PiPolynomialValues.Certificates
