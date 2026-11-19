module

public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! The final rational inputs of the two balanced certificates. These tests
verify the arithmetic of the margins. Analytic enclosures for the input
constants are separate theorems. -/

@[expose] public section

namespace PiPolynomialValues

structure RateData where
  degree : ℕ
  exponent : ℚ
  scale : ℚ
  radius : ℚ
  length : ℚ
  rowSquare : ℚ
  moment : ℚ
  auxDegree : ℚ
  primeCost : ℚ
  baseCost : ℚ
  ordinary : ℚ
  penalty : ℚ
  cost : ℚ
  labelPrice : ℚ

def quadraticRateData : RateData where
  degree := 2
  exponent := 16161227 / 1000000
  scale := 5338833 / 5000000
  radius := 41059 / 250000
  length := 71447 / 5000
  rowSquare := 9027605878701 / 8603662240000
  moment := 329223465754612241123 / 405705865000444800000
  auxDegree := 366805831 / 113280184
  primeCost := 257726971829988489072095961700467913 / 115372605359501490000000000000000000
  baseCost := 481765210105257944324651 / 8603662240000000000000000
  ordinary := -1389460592319205667615142781 / 3667445957000000000000000000
  penalty := 129065494678084437 / 10000000000000000
  cost := 4465339340766734604104922024015627853634448839169133550321809 / 498640400363765439780000000000000000000000000000000000000000
  labelPrice := 2303522168625500513358341 / 250000000000000000000000000000

def cubicRateData : RateData where
  degree := 3
  exponent := 3426527 / 125000
  scale := 10695379 / 10000000
  radius := 1289 / 8000
  length := 120469 / 5000
  rowSquare := 26913156607199 / 27119097760000
  moment := 300145578206662707301 / 205821667047114720000
  auxDegree := 70593193463 / 12547087288
  primeCost := 3852599160392012435325905185444754789930413 / 1520360078006302998247282500000000000000000
  baseCost := 21130280270983035107589 / 216952782080000000000000
  ordinary := -273547871717024862444983179 / 784192955500000000000000000
  penalty := 109962586358075809 / 5000000000000000
  cost := 1568555586708139957147297030664286176840043053105509711273509715277359 / 104519687496006643452839847600000000000000000000000000000000000000000
  labelPrice := 53273322581466834363046167 / 2000000000000000000000000000000

namespace RateData

def target (s : RateData) : ℚ := 1 + s.exponent
def B (s : RateData) : ℚ := s.scale * s.penalty
def δ (s : RateData) : ℚ := s.scale * s.labelPrice
def Y (s : RateData) : ℚ := s.degree - 1
def hStar (s : RateData) : ℚ := s.Y / (s.scale * s.length)
def mainMargin (s : RateData) : ℚ :=
  s.B - (2 * s.B - s.target - s.δ) ^ 2 / (8 * s.B) - (s.auxDegree + s.scale * s.cost)
def loss (s : RateData) : ℚ := (2 * s.B - s.target + s.Y - s.δ) / (4 * s.B)
/-- A lower secondary slope obtained by using the rational upper bound 4 for π. -/
def secondaryLower (s : RateData) : ℚ :=
  1/2 - s.rowSquare / s.length - 4 * s.moment / (2 * s.length * (1 - s.hStar ^ 2))

/-- The two endpoint tests of the whole interval give the two active labels
there. The final inequalities leave strictly positive principal and secondary gains. -/
def passes (s : RateData) (margin : ℚ) : Prop :=
  0 < s.scale ∧ 0 < s.radius ∧ s.radius < 1 ∧ 0 < s.length ∧ 0 < s.moment ∧
  0 < s.hStar ∧ s.hStar < 1 ∧ 0 < s.B ∧ 0 ≤ s.δ ∧ 0 < s.target - s.Y ∧
  s.target + s.δ < 2 * s.B ∧ 2 * s.B < 3 * (s.target - s.Y) + s.δ ∧
  0 ≤ s.baseCost + s.primeCost + s.ordinary ∧ margin < s.mainMargin ∧
  (1 / 12 : ℚ) < s.secondaryLower - s.loss

end RateData

theorem quadratic_rate_tests : quadraticRateData.passes (8 / 100000000) := by
  norm_num [RateData.passes, RateData.mainMargin, RateData.secondaryLower, RateData.loss,
    RateData.target, RateData.hStar, RateData.Y, RateData.B, RateData.δ, quadraticRateData]

theorem cubic_rate_tests : cubicRateData.passes (11 / 100000000) := by
  norm_num [RateData.passes, RateData.mainMargin, RateData.secondaryLower, RateData.loss,
    RateData.target, RateData.hStar, RateData.Y, RateData.B, RateData.δ, cubicRateData]

end PiPolynomialValues
