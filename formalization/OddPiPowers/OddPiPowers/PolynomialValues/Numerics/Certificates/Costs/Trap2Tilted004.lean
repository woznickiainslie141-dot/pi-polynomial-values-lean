module

public import OddPiPowers.PolynomialValues.Numerics.AnchorWords
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Stripes.All
public import OddPiPowers.PolynomialValues.Numerics.Certificates.References.FieldSet2Tilted003
public import OddPiPowers.PolynomialValues.Numerics.Certificates.AnchorPlan2
public import OddPiPowers.PolynomialValues.FourPeriod.Shape

@[expose] public section

namespace PiPolynomialValues.Certificates

/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted004Block000. -/
/- Independently checkable declarations from Paid2Tilted004Block000. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block000Slice000 :
    gridCostBlock 0 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=420952503219079477520000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block000Slice003 :
    gridCostBlock 3 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=420998865473530564360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block000Slice006 :
    gridCostBlock 6 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421286046194795112320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block000Slice009 :
    gridCostBlock 9 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421408441578938286200000 := by decide +kernel

theorem paid2Tilted004Block000 : gridCostBlock 0 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1684645856466343440400000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 0 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block000Slice000 paid2Tilted004Block000Slice003)) paid2Tilted004Block000Slice006)) paid2Tilted004Block000Slice009))
/- Independently checkable declarations from Paid2Tilted004Block012. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block012Slice012 :
    gridCostBlock 12 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421530641205632537040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block012Slice015 :
    gridCostBlock 15 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421354694542834645400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block012Slice018 :
    gridCostBlock 18 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422024320136913394640000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block012Slice021 :
    gridCostBlock 21 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422164849746400239000000 := by decide +kernel

theorem paid2Tilted004Block012 : gridCostBlock 12 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1687074505631780816080000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 12 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 12 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block012Slice012 paid2Tilted004Block012Slice015)) paid2Tilted004Block012Slice018)) paid2Tilted004Block012Slice021))
/- Independently checkable declarations from Paid2Tilted004Block024. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block024Slice024 :
    gridCostBlock 24 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422628246110143748960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block024Slice027 :
    gridCostBlock 27 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421996626487833946440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block024Slice030 :
    gridCostBlock 30 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421712490625059518480000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block024Slice033 :
    gridCostBlock 33 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421712102895005267320000 := by decide +kernel

theorem paid2Tilted004Block024 : gridCostBlock 24 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1688049466118042481200000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 24 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 24 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block024Slice024 paid2Tilted004Block024Slice027)) paid2Tilted004Block024Slice030)) paid2Tilted004Block024Slice033))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted004Block036. -/
/- Independently checkable declarations from Paid2Tilted004Block036. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block036Slice036 :
    gridCostBlock 36 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711763202451872080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block036Slice039 :
    gridCostBlock 39 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711433204531414680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block036Slice042 :
    gridCostBlock 42 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711253784153460160000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block036Slice045 :
    gridCostBlock 45 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711058937232469440000 := by decide +kernel

theorem paid2Tilted004Block036 : gridCostBlock 36 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1686845509128369216360000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 36 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 36 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block036Slice036 paid2Tilted004Block036Slice039)) paid2Tilted004Block036Slice042)) paid2Tilted004Block036Slice045))
/- Independently checkable declarations from Paid2Tilted004Block048. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block048Slice048 :
    gridCostBlock 48 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710916231454906400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block048Slice051 :
    gridCostBlock 51 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710729531730475240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block048Slice054 :
    gridCostBlock 54 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710587483929158440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block048Slice057 :
    gridCostBlock 57 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710477504542491800000 := by decide +kernel

theorem paid2Tilted004Block048 : gridCostBlock 48 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1686842710751657031880000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 48 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 48 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block048Slice048 paid2Tilted004Block048Slice051)) paid2Tilted004Block048Slice054)) paid2Tilted004Block048Slice057))
/- Independently checkable declarations from Paid2Tilted004Block060. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block060Slice060 :
    gridCostBlock 60 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710391230432135000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block060Slice063 :
    gridCostBlock 63 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710391230432135000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block060Slice066 :
    gridCostBlock 66 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710477504542491800000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block060Slice069 :
    gridCostBlock 69 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710587483929158440000 := by decide +kernel

theorem paid2Tilted004Block060 : gridCostBlock 60 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1686841847449335920240000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 60 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 60 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block060Slice060 paid2Tilted004Block060Slice063)) paid2Tilted004Block060Slice066)) paid2Tilted004Block060Slice069))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted004Block072. -/
/- Independently checkable declarations from Paid2Tilted004Block072. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block072Slice072 :
    gridCostBlock 72 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710729531730475240000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block072Slice075 :
    gridCostBlock 75 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421710916231454906400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block072Slice078 :
    gridCostBlock 78 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711058937232469440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block072Slice081 :
    gridCostBlock 81 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711253784153460160000 := by decide +kernel

theorem paid2Tilted004Block072 : gridCostBlock 72 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1686843958484571311240000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 72 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 72 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block072Slice072 paid2Tilted004Block072Slice075)) paid2Tilted004Block072Slice078)) paid2Tilted004Block072Slice081))
/- Independently checkable declarations from Paid2Tilted004Block084. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block084Slice084 :
    gridCostBlock 84 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711433204531414680000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block084Slice087 :
    gridCostBlock 87 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421711763202451872080000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block084Slice090 :
    gridCostBlock 90 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421712102895005267320000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block084Slice093 :
    gridCostBlock 93 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421712490625059518480000 := by decide +kernel

theorem paid2Tilted004Block084 : gridCostBlock 84 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1686847789927048072560000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 84 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 84 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block084Slice084 paid2Tilted004Block084Slice087)) paid2Tilted004Block084Slice090)) paid2Tilted004Block084Slice093))
/- Independently checkable declarations from Paid2Tilted004Block096. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block096Slice096 :
    gridCostBlock 96 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421996626487833946440000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block096Slice099 :
    gridCostBlock 99 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422628246110143748960000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block096Slice102 :
    gridCostBlock 102 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422164849746400239000000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block096Slice105 :
    gridCostBlock 105 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=422024320136913394640000 := by decide +kernel

theorem paid2Tilted004Block096 : gridCostBlock 96 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1688814042481291329040000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 96 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 96 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block096Slice096 paid2Tilted004Block096Slice099)) paid2Tilted004Block096Slice102)) paid2Tilted004Block096Slice105))
/- Bounded arithmetic from Numerics.Certificates.Costs.Paid2Tilted004Block108. -/
/- Independently checkable declarations from Paid2Tilted004Block108. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block108Slice108 :
    gridCostBlock 108 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421354694542834645400000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block108Slice111 :
    gridCostBlock 111 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421530641205632537040000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block108Slice114 :
    gridCostBlock 114 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421408441578938286200000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block108Slice117 :
    gridCostBlock 117 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=421286046194795112320000 := by decide +kernel

theorem paid2Tilted004Block108 : gridCostBlock 108 12 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=1685579823522200580960000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 108 9 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 6 3 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 108 3 3 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block108Slice108 paid2Tilted004Block108Slice111)) paid2Tilted004Block108Slice114)) paid2Tilted004Block108Slice117))
/- Independently checkable declarations from Paid2Tilted004Block120. -/
set_option maxRecDepth 8192 in
theorem paid2Tilted004Block120Slice120 :
    gridCostBlock 120 3 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=420998865473530564360000 := by decide +kernel

set_option maxRecDepth 8192 in
theorem paid2Tilted004Block120Slice123 :
    gridCostBlock 123 2 (fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=280634257471089583120000 := by decide +kernel

theorem paid2Tilted004Block120 : gridCostBlock 120 5 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=701633122944620147480000 := by
  rw [show (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=(fun r => anchorReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r)) from funext (fun r => (anchorReferenceCost_eq _ _ _ anchorPlan2_covers _ r _).symm)]
  exact ((gridCostBlock_join 120 3 2 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block120Slice120 paid2Tilted004Block120Slice123))
/- Bounded arithmetic from Numerics.Certificates.Costs.Trap2Tilted004. -/
theorem trap2Tilted004 : gridCostBlock 0 125 (fun r => quickReferenceCost reference2Tilted004 FourPeriod.quadraticShape.widths anchorPlan2 3256 r (spatialBasis r))=17570018632905260347440000 :=
  ((gridCostBlock_join 0 120 5 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 108 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 96 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 84 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 72 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 60 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 48 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 36 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 24 12 _).symm.trans (congrArg₂ (·+·) ((gridCostBlock_join 0 12 12 _).symm.trans (congrArg₂ (·+·) paid2Tilted004Block000 paid2Tilted004Block012)) paid2Tilted004Block024)) paid2Tilted004Block036)) paid2Tilted004Block048)) paid2Tilted004Block060)) paid2Tilted004Block072)) paid2Tilted004Block084)) paid2Tilted004Block096)) paid2Tilted004Block108)) paid2Tilted004Block120))

end PiPolynomialValues.Certificates
