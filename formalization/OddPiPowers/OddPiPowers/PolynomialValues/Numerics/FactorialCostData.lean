module

public import OddPiPowers.PolynomialValues.Numerics.ShapeLogBounds
public import OddPiPowers.PolynomialValues.Numerics.PrimeTailData

/-! The actual row masses in the factorial rate and the true
logarithm of the inverse sampling radius have the certified costs. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Real

def Shape.massList (s : Shape) := s.rows.map s.rowMassQ

def upperBaseSum (xs : List ℚ) := (xs.map fun a => a^2*(3/2-logTickLo (2*a))).sum

noncomputable def analyticBaseSum (xs : List ℚ) : ℝ := (xs.map fun a => (a : ℝ)^2*(3/2-log (2*(a : ℝ)))).sum

theorem actualBaseSum_le (xs : List ℚ) (h : ∀ a∈xs, 1≤2*a) : analyticBaseSum xs≤(upperBaseSum xs : ℝ) := by
  induction xs with
  | nil => simp [analyticBaseSum,upperBaseSum]
  | cons a xs ih =>
    have HL := (logTick_bounds (2*a) (h _ (by simp))).1
    push_cast at HL
    have HH := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    change (a : ℝ)^2*(3/2-log (2*(a : ℝ)))+analyticBaseSum xs≤
      ((a^2*(3/2-logTickLo (2*a))+upperBaseSum xs : ℚ) : ℝ)
    push_cast
    exact add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub_left HL _) (sq_nonneg _)) HH

def Shape.basePass (s : Shape) (d : RateData) : Bool := decide
  (0<s.totalWidthQ ∧ s.totalWidthQ=d.length ∧ (s.massList.all fun a => decide (1≤2*a))=true ∧
   upperBaseSum s.massList≤2*s.totalWidthQ*d.baseCost ∧ 1≤1/d.radius ∧
   d.penalty≤d.length*logTickLo (1/d.radius)/2)

theorem Shape.basePass_sound (s : Shape) (d : RateData) (hp : s.basePass d=true) :
    analyticBaseSum s.massList/(2*(d.length : ℝ))≤(d.baseCost : ℝ) ∧
    (d.penalty : ℝ)≤(d.length : ℝ)*Real.log (1/(d.radius : ℝ))/2 ∧
    Real.log (1/(d.radius : ℝ))≤(logTickHi (1/d.radius) : ℝ) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := of_decide_eq_true hp
  have hl : 0<(d.length : ℝ) := by exact_mod_cast h₂ ▸ h₁
  have HS := actualBaseSum_le s.massList (fun a ha => of_decide_eq_true (List.all_eq_true.mp h₃ a ha))
  have HU := (Rat.cast_le (K := ℝ)).mpr h₄
  rw [h₂] at HU
  push_cast at HU
  have H := logTick_bounds (1/d.radius) h₅
  have HK := (Rat.cast_le (K := ℝ)).mpr h₆
  push_cast at H HK
  refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,?_,H.2⟩
  · linarith only [HS,HU]
  · linarith only [HK,mul_le_mul_of_nonneg_left H.1 hl.le]

theorem quadratic_factorial_cost_checked : quadraticShape.basePass quadraticRateData=true := by decide +kernel
theorem cubic_factorial_cost_checked : cubicShape.basePass cubicRateData=true := by decide +kernel

end PiPolynomialValues.FourPeriod
