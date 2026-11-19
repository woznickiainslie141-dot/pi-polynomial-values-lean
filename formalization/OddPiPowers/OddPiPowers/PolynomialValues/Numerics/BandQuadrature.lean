module

public import OddPiPowers.PolynomialValues.Numerics.SpatialQuadrature
public import OddPiPowers.PolynomialValues.Numerics.FastQuadrature
public import Mathlib.Data.List.Enum

/-! Rewrite the scalar product over grid nodes as a sum over frequency
cells. The two endpoint prices on each tilted cell use its own center. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def bandCount (ws : List ℕ) (i : ℕ) : ℤ := (ws.map fun w => (bandSpan w).hit i).sum

theorem bandWeights_shift (ws : List ℕ) (d i : ℕ) : (bandWeights ws d).val (i+d)=bandCount ws i := by
  simp [bandWeights,GridWeights.val,bandCount,List.map_map,Function.comp_def,GridSpan.shift_hit]

theorem bandWeights_budget (ws : List ℕ) (d : ℕ) : (bandWeights ws d).budget=ws.length := by
  induction ws with
  | nil => simp [bandWeights,GridWeights.budget]
  | cons w ws ih =>
    change |(1:ℤ)|+(bandWeights ws d).budget=((w::ws).length : ℤ)
    simp [ih,add_comm]

theorem GridWeights.budget_append (a b : GridWeights) : GridWeights.budget (a++b)=a.budget+b.budget := by
  simp [GridWeights.budget]

theorem AnchorPlan.charge_budget (a : AnchorPlan) (d v : ℕ) (fee : ℤ) :
    (a.charges v d fee).budget≤(a.length : ℤ)*|fee| := by
  induction a with
  | nil => simp [charges,GridWeights.budget]
  | cons p a ih =>
    change |(if p.2=v then 0 else fee)|+(AnchorPlan.charges a v d fee).budget≤((p::a).length : ℤ)*|fee|
    rw [List.length_cons,Nat.cast_succ,add_mul,one_mul]
    split_ifs <;> (try simp only [abs_zero]) <;> linarith only [ih,abs_nonneg fee]

theorem bandCount_range (ws : List ℕ) (i : ℕ) : 0≤bandCount ws i ∧ bandCount ws i≤ws.length := by
  induction ws with
  | nil => simp [bandCount]
  | cons w ws ih =>
    change 0≤(bandSpan w).hit i+bandCount ws i ∧ (bandSpan w).hit i+bandCount ws i≤((w::ws).length : ℤ)
    rw [List.length_cons,Nat.cast_succ]
    unfold GridSpan.hit
    split_ifs <;> constructor <;> omega

theorem band_endpoint_shift (ws : List ℕ) (h : ∀ w∈ws, w≤10000) (d : ℕ) (hd : d≤1) (f : ℕ → ℤ) :
    (∑ i ∈ range 80001, (bandWeights ws d).val i*f i)=∑ i ∈ range 80000, bandCount ws i*f (i+d) := by
  have hzero : bandCount ws 80000=0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    have := h w hw
    exact if_neg (by dsimp [bandSpan]; omega)
  have hstart : (bandWeights ws 1).val 0=0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hp
    simp [GridSpan.hit,GridSpan.shift]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl|rfl
  · have H (i : ℕ) : (bandWeights ws 0).val i=bandCount ws i := bandWeights_shift ws 0 i
    rw [sum_range_succ (n := 80000),H 80000,hzero,zero_mul,add_zero]
    simp only [H,Nat.add_zero]
  · rw [sum_range_succ' (n := 80000),hstart,zero_mul,add_zero]
    simp only [bandWeights_shift]

def gridDot (rows : List PricedSpatialLane) (w : GridWeights) :=
  ∑ i ∈ range 80001, w.val i*gridEnvelope rows i

theorem gridDot_append (rows : List PricedSpatialLane) (a b : GridWeights) :
    gridDot rows (a++b)=gridDot rows a+gridDot rows b := by
  simp [gridDot,GridWeights.val_append,add_mul,sum_add_distrib]

theorem gridDot_bands (left right : List PricedSpatialLane) (ws : List ℕ) (h : ∀ w∈ws, w≤10000) :
    gridDot left (bandWeights ws 0)+gridDot right (bandWeights ws 1)=
      ∑ i ∈ range 80000, bandCount ws i*(gridEnvelope left i+gridEnvelope right (i+1)) := by
  rw [gridDot,gridDot,band_endpoint_shift ws h 0 (by decide),band_endpoint_shift ws h 1 (by decide)]
  simp only [Nat.add_zero,mul_add,sum_add_distrib]

def cellTrap (rows : List SpatialLane) (ws : List ℕ) (a : AnchorPlan) (price : ℤ) (i : ℕ) :=
  let base := gridEnvelope (bareLanes rows) i+gridEnvelope (bareLanes rows) (i+1)
  if price=0 then bandCount ws i*base
  else bandCount (ws.take 1) i*base+bandCount ws.tail i*
    (gridEnvelope (feeLanes rows a 0 price) i+gridEnvelope (feeLanes rows a 1 price) (i+1))

theorem bareLane_checks (rows : List SpatialLane) (hd : ∀ v∈rows, v.passes=true)
    (p : PricedSpatialLane) (hp : p∈bareLanes rows) : p.lane.passes=true ∧ p.surcharge.budget≤10^27 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
  exact ⟨hd _ hv,by change (0 : ℤ)≤10^27; decide⟩

theorem feeLane_checks (rows : List SpatialLane) (hd : ∀ v∈rows, v.passes=true) (a : AnchorPlan)
    (d : ℕ) (price : ℤ) (hc : (a.length : ℤ)*|price*400000000000|≤10^27)
    (p : PricedSpatialLane) (hp : p∈feeLanes rows a d price) : p.lane.passes=true ∧ p.surcharge.budget≤10^27 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have h : ∀ q∈rows.zipIdx, q.1.passes=true := List.forall_mem_zipIdx'.mpr (fun i hi =>
    hd _ (List.getElem_mem hi))
  exact ⟨h _ hq,(a.charge_budget _ _ _).trans hc⟩

attribute [local irreducible] Finset.range gridDot gridEnvelope bandCount bandWeights bareLanes feeLanes stripeWeightedCost

theorem gridCostBlock_zero (n : ℕ) (f : ℕ → ℤ) : gridCostBlock 0 n f=∑ k ∈ range n, f k := by
  simp only [gridCostBlock_eq,Nat.zero_add]

theorem reference_trapezoid (basis : (r : ℕ) → StripeBasis r) (rows : List SpatialLane) (ws : List ℕ)
    (a : AnchorPlan) (price : ℤ) (hd : ∀ v∈rows, v.passes=true) (hws : ∀ w∈ws, w≤10000)
    (hw : ws.length≤50) (hc : (a.length : ℤ)*|price*400000000000|≤10^27) :
    gridCostBlock 0 125 (fun r => quickReferenceCost rows ws a price r (basis r))=
      ∑ i ∈ range 80000, cellTrap rows ws a price i := by
  let F := bareLanes rows
  let P := feeLanes rows a 0 price
  let Q := feeLanes rows a 1 price
  have hbare (w : GridWeights) (h : w.budget≤100) : allStripeCost basis F w=gridDot F w := by
    unfold gridDot
    exact allStripeCost_sound basis _ _ (fun p hp => (bareLane_checks rows hd p hp).1)
      (fun p hp => (bareLane_checks rows hd p hp).2) h
  have hfee (d : ℕ) (w : GridWeights) (h : w.budget≤100) :
      allStripeCost basis (feeLanes rows a d price) w=gridDot (feeLanes rows a d price) w := by
    unfold gridDot
    exact allStripeCost_sound basis _ _ (fun p hp => (feeLane_checks rows hd a d price hc p hp).1)
      (fun p hp => (feeLane_checks rows hd a d price hc p hp).2) h
  have hboth (xs : List ℕ) (h : xs.length≤50) : GridWeights.budget (bandWeights xs 0++bandWeights xs 1)≤100 := by
    rw [GridWeights.budget_append,bandWeights_budget,bandWeights_budget]
    omega
  rw [gridCostBlock_zero]
  simp only [quickReferenceCost_eq]
  by_cases h : price=0
  · simp only [referenceStripeCost,cellTrap,h,if_true]
    exact (hbare (bandWeights ws 0++bandWeights ws 1) (hboth ws hw)).trans
      ((gridDot_append F (bandWeights ws 0) (bandWeights ws 1)).trans (gridDot_bands F F ws hws))
  · simp only [referenceStripeCost,cellTrap,if_neg h,sum_add_distrib]
    have ht : ∀ w∈ws.take 1, w≤10000 := fun w hm => hws w (List.mem_of_mem_take hm)
    have hs : ∀ w∈ws.tail, w≤10000 := fun w hm => hws w (List.mem_of_mem_tail hm)
    have hb (d : ℕ) : (bandWeights ws.tail d).budget≤100 := by
      rw [bandWeights_budget,List.length_tail]
      omega
    have hb₁ := (hbare (bandWeights (ws.take 1) 0++bandWeights (ws.take 1) 1)
      (hboth (ws.take 1) (by simp))).trans
        ((gridDot_append F (bandWeights (ws.take 1) 0) (bandWeights (ws.take 1) 1)).trans
          (gridDot_bands F F _ ht))
    have hb₂ := (congrArg₂ (·+·) (hfee 0 _ (hb 0)) (hfee 1 _ (hb 1))).trans (gridDot_bands P Q _ hs)
    exact (add_assoc _ _ _).trans (congrArg₂ (·+·) hb₁ hb₂)

end PiPolynomialValues
