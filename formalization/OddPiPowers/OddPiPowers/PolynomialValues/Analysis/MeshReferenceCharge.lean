module

public import OddPiPowers.PolynomialValues.Numerics.MeshLagBound
public import OddPiPowers.PolynomialValues.Numerics.SpatialLane

/-! An integer mesh row is a genuine signed reference charge on the
frequency interval. Its kernel potential and full self-interaction
are exactly the quantities checked with the two spatial primitives. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Filter
open scoped Topology

noncomputable def meshEdge {n step : ℕ} (h : (n-1)*step≤80000) (i : Fin n) : FrequencyInterval :=
  ⟨(i.val : ℝ)*step/40000-1,by
    have hb := (Nat.mul_le_mul_right step (show i.val≤n-1 by have := i.isLt; omega)).trans h
    have hh : (i.val : ℝ)*step≤80000 := by exact_mod_cast hb
    constructor
    · linarith only [show 0≤(i.val : ℝ)*step by positivity]
    · linarith only [hh]⟩

noncomputable def meshReference {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ) :=
  edgeCharge (meshEdge h) (fun i => (d i.val : ℝ)/100000)

noncomputable def meshLimitPotential {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ) :=
  stepPotential (fun i => tailInterval (meshEdge h i)) (fun i => (d i.val : ℝ)/100000)

theorem meshJump_zero {n : ℕ} (d : ℕ → ℤ) (hd : ∑ i ∈ range n, d i=0) :
    ∑ i : Fin n, (d i.val : ℝ)/100000=0 := by
  rw [← sum_div,Fin.sum_univ_eq_sum_range (fun j => (d j : ℝ)) n,← Int.cast_sum,hd]
  simp

theorem meshReference_potential {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ)
    (hd : ∑ i ∈ range n, d i=0) (z : FrequencyInterval) :
    meshLimitPotential h d z=∑ j ∈ range n, (d j : ℝ)/100000*logPrimitive ((z : ℝ)+1-j*step/40000) := by
  rw [meshLimitPotential,edge_potential _ _ (meshJump_zero d hd)]
  change (∑ i : Fin n, (d i.val : ℝ)/100000*logPrimitive ((z : ℝ)-((i.val : ℝ)*step/40000-1)))=_
  rw [Fin.sum_univ_eq_sum_range (fun i => (d i : ℝ)/100000*logPrimitive ((z : ℝ)-((i : ℝ)*step/40000-1))) n]
  apply sum_congr rfl
  intro j _
  rw [show (z : ℝ)-((j : ℝ)*step/40000-1)=(z : ℝ)+1-j*step/40000 by ring]

theorem meshReference_self {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ)
    (hd : ∑ i ∈ range n, d i=0) :
    meshReference h d (meshLimitPotential h d) = -meshPairEnergy n step d/100000^2 := by
  rw [meshReference,meshLimitPotential,edge_interaction _ _ _ _ (meshJump_zero d hd) (meshJump_zero d hd)]
  let term (i j : ℕ) := (d i : ℝ)*d j*energyPrimitive (((i : ℝ)-j)*step/40000)
  have he (i j : Fin n) : (d i.val : ℝ)/100000*((d j.val : ℝ)/100000)*
      energyPrimitive ((meshEdge h j : ℝ)-(meshEdge h i : ℝ))=term i.val j.val/100000^2 := by
    have hz : (meshEdge h j : ℝ)-(meshEdge h i : ℝ) = -(((i.val : ℝ)-j.val)*step/40000) := by
      change (j.val : ℝ)*step/40000-1-((i.val : ℝ)*step/40000-1)=_
      ring
    rw [hz,energyPrimitive_neg]
    unfold term
    ring
  simp only [he,← sum_div]
  have hf (i : Fin n) := Fin.sum_univ_eq_sum_range (term i.val) n
  simp only [hf]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, term i j) n,neg_div]
  rfl

theorem meshReference_radial_limit {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ)
    {η : Type*} {F : Filter η} {r : η → ℝ} (hr : ∀ i, 0<r i) (hr1 : ∀ i, r i<1) (ht : Tendsto r F (𝓝 1)) :
    Tendsto (fun i => radialPotential unitFrequency (r i) (meshReference h d)) F (𝓝 (meshLimitPotential h d)) :=
  stepPotential_limit hr hr1 ht _ _

theorem lane_real_potential (v : SpatialLane) (hv : v.passes=true) (z : FrequencyInterval) :
    v.realField z=(v.slope : ℝ)/100000*(z : ℝ)+meshLimitPotential (n := 641) (step := 125) (by decide) v.jump z-
      (v.β : ℝ)/100000 := by
  rw [SpatialLane.realField,meshReference_potential _ _ (v.sound hv).2.1]
  rw [add_div,sub_div,Finset.sum_div]
  have he (j : ℕ) : (v.jump j : ℝ)*logPrimitive ((z : ℝ)+1-125*j/40000)/100000=
      (v.jump j : ℝ)/100000*logPrimitive ((z : ℝ)+1-j*125/40000) := by rw [mul_comm (j : ℝ) 125]; ring
  simp only [he]
  ring

end PiPolynomialValues
