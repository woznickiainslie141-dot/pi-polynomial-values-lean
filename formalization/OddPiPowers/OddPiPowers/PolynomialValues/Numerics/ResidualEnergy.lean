module

public import OddPiPowers.PolynomialValues.Numerics.SparseEnergyGrid
public import OddPiPowers.PolynomialValues.Numerics.MeshLagBound

/-! Regular node charges and the signed residual use the same density
jumps as the first-primitive fields. Only the band endpoints are added
on the finer grid. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

def totalJump (rows : List SpatialLane) (j : ℕ) : ℤ := (rows.map fun v => v.jump j).sum
def jumpBudget (rows : List SpatialLane) : ℤ := (rows.map SpatialLane.norm).sum
def residualJump (rows : List SpatialLane) (ws : List ℕ) (i : ℕ) := bandJumps ws i-sparse125 (totalJump rows) i

def residualWord (b : ℤ) (rows : List SpatialLane) (ws : List ℕ) :=
  bandJumpWord b ws-coarseWord (b^125) (totalJump rows)
def residualReverse (b : ℤ) (rows : List SpatialLane) (ws : List ℕ) :=
  -bandJumpWord b ws-coarseWord (b^125) (fun j => totalJump rows (640-j))

theorem residual_words (b : ℤ) (rows : List SpatialLane) (ws : List ℕ) (h : ∀ w∈ws, w≤10000) :
    residualWord b rows ws=packEval b 80001 (residualJump rows ws) ∧
    residualReverse b rows ws=packEval b 80001 (fun i => residualJump rows ws (80000-i)) := by
  rw [residualWord,residualReverse,bandJumpWord_eq b ws h,coarseWord_eq,coarseWord_eq,packEval_eq,packEval_eq]
  refine ⟨?_,?_⟩
  · rw [← sparse125_pack,← packedSum_sub]
    rfl
  · rw [← sparse125_pack]
    have H : -packedSum b 80001 (bandJumps ws)=packedSum b 80001 (fun i => -bandJumps ws i) := by
      simp [packedSum,sum_neg_distrib]
    rw [H,← packedSum_sub]
    apply packedSum_congr
    intro i hi
    rw [residualJump,bandJumps_reflect ws h hi,sparse125_reflect hi]

theorem totalJump_norm (rows : List SpatialLane) (h : ∀ v∈rows, v.passes=true) :
    (∑ j ∈ range 641, |totalJump rows j|)≤jumpBudget rows := by
  induction rows with
  | nil => simp [totalJump,jumpBudget]
  | cons v rows ih =>
    have hv := (v.sound (h v (by simp))).2.2.1
    have hr := ih (fun w hw => h _ (List.mem_cons_of_mem _ hw))
    change (∑ j ∈ range 641, |v.jump j+totalJump rows j|)≤v.norm+jumpBudget rows
    apply (sum_le_sum (s := range 641) (fun j _ => abs_add_le (v.jump j) (totalJump rows j))).trans
    rw [sum_add_distrib,← hv]
    exact add_le_add le_rfl hr

theorem bandJumps_norm (ws : List ℕ) (h : ∀ w∈ws, w≤10000) :
    (∑ i ∈ range 80001, |bandJumps ws i|)≤200000*(ws.length : ℤ) := by
  induction ws with
  | nil => simp [bandJumps]
  | cons w ws ih =>
    have hw := h w (by simp)
    have hws := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    let A := pointJump (40000-4*w) 100000
    let B := pointJump (40000+4*w) 100000
    have H (i : ℕ) : |bandJumps (w::ws) i|≤|A i|+|B i|+|bandJumps ws i| := by
      change |(A i-B i)+bandJumps ws i|≤_
      exact (abs_add_le _ _).trans (add_le_add (abs_sub (A i) (B i)) le_rfl)
    apply (sum_le_sum (s := range 80001) (fun i _ => H i)).trans
    rw [sum_add_distrib,sum_add_distrib]
    dsimp only [A,B]
    rw [pointJump_norm (by omega),pointJump_norm (by omega)]
    simp only [List.length_cons,Nat.cast_succ,abs_of_nonneg (by decide : (0:ℤ)≤100000)]
    omega

theorem residual_norm (rows : List SpatialLane) (ws : List ℕ) (hd : ∀ v∈rows, v.passes=true)
    (h : ∀ w∈ws, w≤10000) :
    (∑ i ∈ range 80001, |residualJump rows ws i|)≤200000*(ws.length : ℤ)+jumpBudget rows := by
  apply (sum_le_sum (s := range 80001) (fun i _ => abs_sub (bandJumps ws i) (sparse125 (totalJump rows) i))).trans
  have H (i : ℕ) : |sparse125 (totalJump rows) i|=sparse125 (fun j => |totalJump rows j|) i := by
    by_cases hh : i%125=0 <;> simp [sparse125,hh]
  simp only [sum_add_distrib,H,sum_sparse125]
  exact add_le_add (bandJumps_norm ws h) (totalJump_norm rows hd)

def regularEnergy (basis : EnergySection 641 125 0 641) (v : SpatialLane) :=
  lagEnergyWord 641 (coarseWord energyBase v.jump) (coarseWord energyBase (fun j => v.jump (640-j))) basis.word 1

def residualEnergy (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ) :=
  lagEnergyWord 80001 (residualWord energyBase rows ws) (residualReverse energyBase rows ws) basis.word (-1)

theorem abs_le_range_sum {n : ℕ} (a : ℕ → ℤ) {i : ℕ} (hi : i<n) :
    |a i|≤∑ j ∈ range n, |a j| := single_le_sum (fun j _ => abs_nonneg (a j)) (mem_range.mpr hi)

theorem regularEnergy_upper (basis : EnergySection 641 125 0 641) (v : SpatialLane) (hv : v.passes=true) :
    10^12*meshPairEnergy 641 125 v.jump≤(regularEnergy basis v : ℝ) := by
  obtain ⟨_,_,hn,hb,_,_⟩ := v.sound hv
  have hsum : (∑ j ∈ range 641, |v.jump j|)≤10^13 := hn.symm.trans_le (by omega)
  have hrev : (∑ j ∈ range 641, |v.jump (640-j)|)≤10^13 := by
    rw [sum_range_reflect (fun j => |v.jump j|) 641]
    exact hsum
  have H := signed_mesh_energy_upper (n := 641) (step := 125) (by decide) (by decide) (by decide)
    v.jump 1 (by decide) (fun i hi => (abs_le_range_sum v.jump hi).trans hsum) hrev
    ((coarseWord_eq energyBase v.jump).trans (packEval_eq _ _ _).symm)
    ((coarseWord_eq energyBase _).trans (packEval_eq _ _ _).symm) basis.complete
  simpa only [Int.cast_one,one_mul,regularEnergy] using H

theorem residualEnergy_upper (basis : EnergySection 80001 1 0 80001) (rows : List SpatialLane) (ws : List ℕ)
    (hd : ∀ v∈rows, v.passes=true) (hw : ∀ w∈ws, w≤10000) (hn : 200000*(ws.length : ℤ)+jumpBudget rows≤10^13) :
    -(10^12*meshPairEnergy 80001 1 (residualJump rows ws))≤(residualEnergy basis rows ws : ℝ) := by
  have h := (residual_norm rows ws hd hw).trans hn
  have hr : (∑ i ∈ range 80001, |residualJump rows ws (80000-i)|)≤10^13 := by
    rw [sum_range_reflect (fun i => |residualJump rows ws i|) 80001]
    exact h
  have ⟨hx,hy⟩ := residual_words energyBase rows ws hw
  have H := signed_mesh_energy_upper (n := 80001) (step := 1) (by decide) (by decide) (by decide)
    _ (-1) (by decide) (fun i hi => (abs_le_range_sum _ hi).trans h) hr hx hy basis.complete
  simpa only [Int.cast_neg,Int.cast_one,neg_mul,one_mul,residualEnergy] using H

end PiPolynomialValues
