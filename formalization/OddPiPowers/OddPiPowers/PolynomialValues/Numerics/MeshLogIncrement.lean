module

public import OddPiPowers.PolynomialValues.Analysis.OddSeriesBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Integer outward rounding for the successive mesh logarithms.
The truncation length can vary at each step. -/

@[expose] public section

namespace PiPolynomialValues

open Finset Real

def meshLogScale : ℕ := 10^23

def meshTermDen (i j : ℕ) := (2*j+1)*(2*i+1)^(2*j+1)

def meshTermFloor (i j : ℕ) := 2*meshLogScale/meshTermDen i j

def meshIncFloor (i n : ℕ) := ∑ j ∈ range n, meshTermFloor i j

theorem meshTermDen_pos (i j : ℕ) : 0<meshTermDen i j := by unfold meshTermDen; positivity

theorem meshTerm_floor_bounds (i j : ℕ) :
    (meshTermFloor i j : ℝ) ≤ 2*meshLogScale/(meshTermDen i j : ℝ) ∧
      2*meshLogScale/(meshTermDen i j : ℝ) ≤ (meshTermFloor i j : ℝ)+1 := by
  have hp : 0<(meshTermDen i j : ℝ) := by exact_mod_cast meshTermDen_pos i j
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact_mod_cast Nat.div_mul_le_self (2*meshLogScale) (meshTermDen i j)
  · apply (div_le_iff₀ hp).mpr
    have h := Nat.lt_mul_div_succ (2*meshLogScale) (meshTermDen_pos i j)
    rw [Nat.mul_comm (meshTermDen i j) (_+1)] at h
    exact_mod_cast h.le

theorem log_increment_odd {i : ℕ} (hi : 0 < i) :
    Real.log (i+1 : ℕ)-Real.log (i : ℝ) = 2*halfLogRatio ((2*(i : ℝ)+1)⁻¹) := by
  let I := (i : ℝ)
  have hp : 0<I := by dsimp [I]; exact_mod_cast hi
  have ht : 0<2*I+1 := by linarith
  have hu : (2*I+1)⁻¹ < 1 := (inv_lt_one₀ ht).mpr (by linarith)
  have hd : 0<1-(2*I+1)⁻¹ := by linarith
  have hn : 0<1+(2*I+1)⁻¹ := by positivity
  have hdiv : (1+(2*I+1)⁻¹)/(1-(2*I+1)⁻¹)=(I+1)/I := by
    field_simp
    <;> ring
  push_cast
  change Real.log (I+1)-Real.log I=2*halfLogRatio ((2*I+1)⁻¹)
  rw [halfLogRatio,← Real.log_div hn.ne' hd.ne',hdiv,Real.log_div (by linarith) hp.ne']
  ring

theorem mesh_inc_bounds {i n : ℕ} (hi : 0 < i) (htail : 2*meshLogScale ≤ meshTermDen i n) :
    (meshIncFloor i n : ℝ) ≤ meshLogScale*(Real.log (i+1 : ℕ)-Real.log (i : ℝ)) ∧
    meshLogScale*(Real.log (i+1 : ℕ)-Real.log (i : ℝ)) ≤ (meshIncFloor i n : ℝ)+n+2 := by
  let x := (2*(i : ℝ)+1)⁻¹
  have hd : 0<2*(i : ℝ)+1 := by positivity
  have hx : 0≤x := (inv_pos.mpr hd).le
  have hxi : x≤1/3 := by
    rw [show x=1/(2*(i : ℝ)+1) by simp [x,one_div]]
    have hh : (1 : ℝ) ≤ i := by exact_mod_cast hi
    exact (div_le_div_iff₀ hd (by norm_num)).mpr (by linarith)
  have hb := halfLogRatio_odd_bounds hx (by linarith) n
  let T (j : ℕ) := 2*(meshLogScale : ℝ)/(meshTermDen i j : ℝ)
  have hterm (j : ℕ) : T j=2*meshLogScale*(x^(2*j+1)/(2*j+1 : ℕ)) := by
    dsimp [T,meshTermDen,x]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  have hs : (∑ j ∈ range n, T j)=2*meshLogScale*arcOdd 1 n x := by
    rw [arcOdd,mul_sum]
    apply sum_congr rfl
    intro j _
    simpa using hterm j
  have hl := sum_le_sum (s := range n) (fun j _ => (meshTerm_floor_bounds i j).1)
  have hu := sum_le_sum (s := range n) (fun j _ => (meshTerm_floor_bounds i j).2)
  change (∑ j ∈ range n, (meshTermFloor i j : ℝ)) ≤ ∑ j ∈ range n, T j at hl
  change (∑ j ∈ range n, T j) ≤ ∑ j ∈ range n, ((meshTermFloor i j : ℝ)+1) at hu
  rw [hs] at hl hu
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one] at hu
  have ht : T n ≤ 1 := (div_le_one (by exact_mod_cast meshTermDen_pos i n)).mpr (by exact_mod_cast htail)
  have hden : 1/2 ≤ 1-x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hxi) (show 0≤1/3+x by linarith)]
  have herr : 2*meshLogScale*(x^(2*n+1)/(((2*n+1 : ℕ) : ℝ)*(1-x^2))) ≤ 2 := by
    rw [show 2*meshLogScale*(x^(2*n+1)/(((2*n+1 : ℕ) : ℝ)*(1-x^2))) = T n/(1-x^2) by
      rw [hterm]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [log_increment_odd hi]
  change _ ≤ (meshLogScale : ℝ)*(2*halfLogRatio x) ∧ _ ≤ _
  simp only [meshIncFloor,Nat.cast_sum]
  have hp : 0≤2*(meshLogScale : ℝ) := by positivity
  constructor
  · linarith only [hl,mul_le_mul_of_nonneg_left hb.1 hp]
  · linarith only [hu,herr,mul_le_mul_of_nonneg_left hb.2 hp]

end PiPolynomialValues
