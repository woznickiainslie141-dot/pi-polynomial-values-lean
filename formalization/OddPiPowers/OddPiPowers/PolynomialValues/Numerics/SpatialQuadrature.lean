module

public import OddPiPowers.PolynomialValues.Numerics.WeightedEnvelope

/-! Quadrature weights follow the actual band widths. Each non-base
layer may have a distinct charge on the two ends of a cell because
its center is chosen on the cell itself. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def GridWeights.budget (w : GridWeights) : ℤ := (w.map fun a => |a.2|).sum

theorem GridWeights.val_abs (w : GridWeights) (i : ℕ) : |w.val i|≤w.budget := by
  induction w with
  | nil => simp [val,budget]
  | cons a w ih =>
    change |a.2*a.1.hit i+GridWeights.val w i|≤|a.2|+GridWeights.budget w
    apply (abs_add_le _ _).trans
    apply add_le_add _ ih
    by_cases h : a.1.lo ≤ i ∧ i<a.1.hi <;> simp [GridSpan.hit,h,abs_nonneg]

theorem GridWeights.val_append (w v : GridWeights) (i : ℕ) :
    GridWeights.val (w++v) i=w.val i+v.val i := by simp [val]

def gridEnvelope (rows : List PricedSpatialLane) (i : ℕ) :=
  stripeEnvelopeValue rows (i%125) (i/125)

theorem stripe_position {r : ℕ} (hr : r<125) (k : ℕ) :
    (r+125*k)%125=r ∧ (r+125*k)/125=k := by omega

theorem grid_position (i : ℕ) (hi : i≤80000) : i/125<stripeCount (i%125) := by
  unfold stripeCount
  split <;> omega

theorem gridEnvelope_dominates {rows : List PricedSpatialLane} {v : PricedSpatialLane} (hv : v∈rows)
    (hp : v.lane.passes=true) (i : ℕ) (hi : i≤80000) :
    v.lane.realField ((i : ℝ)/40000-1)+(v.surcharge.val i : ℝ)/(40000*100000*10^9) ≤
      (gridEnvelope rows i : ℝ)/(40000*100000*10^9) := by
  have hm := maxWithFloor_ge (-(10^28)) (fun p : PricedSpatialLane => p.sample (i%125) (i/125)) rows hv
  change v.sample (i%125) (i/125)≤gridEnvelope rows i at hm
  have hn : i%125+125*(i/125)=i := by omega
  have hn' : ((i%125 : ℕ) : ℝ)+125*(i/125 : ℕ)=(i : ℝ) := by exact_mod_cast hn
  have h := v.lane.sample_upper hp (Nat.mod_lt i (by decide : 0<125)) (grid_position i hi)
  rw [hn'] at h
  rw [PricedSpatialLane.sample,hn] at hm
  have hc : ((v.lane.sample (i%125) (i/125) : ℝ)+(v.surcharge.val i : ℝ))≤(gridEnvelope rows i : ℝ) := by exact_mod_cast hm
  linarith only [hc,h]

def allStripeCost (basis : (r : ℕ) → StripeBasis r) (rows : List PricedSpatialLane) (w : GridWeights) :=
  ∑ r ∈ range 125, stripeWeightedCost rows w r (basis r)

theorem allStripeCost_sound (basis : (r : ℕ) → StripeBasis r) (rows : List PricedSpatialLane)
    (w : GridWeights) (h₁ : ∀ p∈rows, p.lane.passes=true)
    (h₂ : ∀ p∈rows, p.surcharge.budget≤10^27) (hw : w.budget≤100) :
    allStripeCost basis rows w=∑ i ∈ range 80001, w.val i*gridEnvelope rows i := by
  rw [allStripeCost,← sum_full_stripes (fun i => w.val i*gridEnvelope rows i)]
  apply sum_congr rfl
  intro r hr
  have hr' := mem_range.mp hr
  rw [stripeWeightedCost_sound rows w hr' _ h₁ (fun p hp k _ => (p.surcharge.val_abs _).trans (h₂ p hp))
    (fun _ _ => (w.val_abs _).trans hw)]
  apply sum_congr rfl
  intro k _
  simp only [gridEnvelope,(stripe_position hr' k).1,(stripe_position hr' k).2]

def GridSpan.shift (s : GridSpan) (d : ℕ) : GridSpan := ⟨s.lo+d,s.hi+d⟩

theorem GridSpan.shift_hit (s : GridSpan) (i d : ℕ) : (s.shift d).hit (i+d)=s.hit i := by
  simp only [shift,hit,Nat.add_le_add_iff_right,Nat.add_lt_add_iff_right]

def bandSpan (w : ℕ) : GridSpan := ⟨40000-4*w,40000+4*w⟩
def bandWeights (widths : List ℕ) (d : ℕ) : GridWeights :=
  widths.map fun w => ((bandSpan w).shift d,1)

abbrev AnchorPlan := List (GridSpan × ℕ)

def AnchorPlan.covers (a : AnchorPlan) (l h : ℕ) : Bool := match a with
  | [] => decide (l=h)
  | p::ps => decide (p.1.lo=l ∧ l<p.1.hi) && covers ps p.1.hi h

def AnchorPlan.center (a : AnchorPlan) (i : ℕ) : ℕ := match a with
  | [] => 0
  | p::ps => if p.1.lo ≤ i ∧ i<p.1.hi then p.2 else center ps i

def AnchorPlan.charges (a : AnchorPlan) (v d : ℕ) (fee : ℤ) : GridWeights :=
  a.map fun p => (p.1.shift d,if p.2=v then 0 else fee)

theorem AnchorPlan.charge_nonneg (a : AnchorPlan) (v d i : ℕ) {fee : ℤ} (hf : 0≤fee) :
    0≤(a.charges v d fee).val i := by
  induction a with
  | nil => simp [charges,GridWeights.val]
  | cons p a ih =>
    change 0≤(if p.2=v then 0 else fee)*(p.1.shift d).hit i+(AnchorPlan.charges a v d fee).val i
    apply add_nonneg _ ih
    apply mul_nonneg
    · split <;> omega
    · unfold GridSpan.hit
      split <;> decide

theorem AnchorPlan.charge_lower {a : AnchorPlan} {l h i : ℕ} (hc : a.covers l h=true) (hl : l ≤ i) (hu : i<h)
    (v d : ℕ) {fee : ℤ} (hf : 0≤fee) :
    (if a.center i=v then 0 else fee)≤(a.charges v d fee).val (i+d) := by
  induction a generalizing l with
  | nil =>
    have he : l=h := of_decide_eq_true hc
    omega
  | cons p a ih =>
    simp only [covers,Bool.and_eq_true,decide_eq_true_eq] at hc
    change (if AnchorPlan.center (p::a) i=v then 0 else fee)≤
      (if p.2=v then 0 else fee)*(p.1.shift d).hit (i+d)+(AnchorPlan.charges a v d fee).val (i+d)
    rw [GridSpan.shift_hit]
    by_cases h : p.1.lo ≤ i ∧ i<p.1.hi
    · simp only [center,GridSpan.hit,if_pos h,mul_one]
      linarith only [AnchorPlan.charge_nonneg a v d (i+d) hf]
    · simp only [center,GridSpan.hit,if_neg h,mul_zero,zero_add]
      exact ih hc.2 (by omega)

def bareLanes (rows : List SpatialLane) : List PricedSpatialLane := rows.map fun v => ⟨v,[]⟩

def feeLanes (rows : List SpatialLane) (a : AnchorPlan) (d : ℕ) (price : ℤ) : List PricedSpatialLane :=
  rows.zipIdx.map fun p => ⟨p.1,a.charges p.2 d (price*400000000000)⟩

def referenceStripeCost (rows : List SpatialLane) (widths : List ℕ) (a : AnchorPlan) (price : ℤ)
    (r : ℕ) (basis : StripeBasis r) : ℤ :=
  if price=0 then stripeWeightedCost (bareLanes rows) (bandWeights widths 0++bandWeights widths 1) r basis
  else
    stripeWeightedCost (bareLanes rows) (bandWeights (widths.take 1) 0++bandWeights (widths.take 1) 1) r basis+
    stripeWeightedCost (feeLanes rows a 0 price) (bandWeights widths.tail 0) r basis+
    stripeWeightedCost (feeLanes rows a 1 price) (bandWeights widths.tail 1) r basis

end PiPolynomialValues
