module

public import OddPiPowers.PolynomialValues.Analysis.MeshReferenceCharge
public import OddPiPowers.PolynomialValues.Analysis.BandCharge
public import OddPiPowers.PolynomialValues.Numerics.ResidualEnergy

/-! The dense energy witness is the total continuous band charge minus
the sum of the individual reference charges, including every band edge. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

noncomputable def tailTest (i step : ℕ) (f : C(FrequencyInterval,ℝ)) :=
  intervalCharge frequencyProjection ((i : ℝ)*step/40000-1) 1 f

theorem meshReference_apply {n step : ℕ} (h : (n-1)*step≤80000) (d : ℕ → ℤ) (f : C(FrequencyInterval,ℝ)) :
    meshReference h d f=∑ i ∈ range n, (d i : ℝ)/100000*tailTest i step f := by
  simp only [meshReference,edgeCharge,stepCharge,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,tailInterval,meshEdge,tailTest]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (d i : ℝ)/100000*tailTest i step f) n

theorem apply_pointJump {p n : ℕ} (hp : p<n) (v : ℤ) (F : ℕ → ℝ) :
    (∑ i ∈ range n, ((pointJump p v i : ℤ) : ℝ)*F i)=(v : ℝ)*F p := by
  simp [pointJump,ite_mul,Finset.mem_range.mpr hp]

theorem apply_bandJumps (ws : List ℕ) (hw : ∀ w∈ws, w≤10000) (F : ℕ → ℝ) :
    (∑ i ∈ range 80001, ((bandJumps ws i : ℤ) : ℝ)*F i)=
      100000*(ws.map fun w => F (40000-4*w)-F (40000+4*w)).sum := by
  induction ws with
  | nil => simp [bandJumps]
  | cons w ws ih =>
    have hh := hw w (by simp)
    have H (i : ℕ) : bandJumps (w::ws) i=pointJump (40000-4*w) 100000 i-
        pointJump (40000+4*w) 100000 i+bandJumps ws i := rfl
    simp only [H,Int.cast_add,Int.cast_sub,add_mul,sub_mul,sum_add_distrib,sum_sub_distrib,
      apply_pointJump (show 40000-4*w<80001 by omega),apply_pointJump (show 40000+4*w<80001 by omega),
      Int.cast_ofNat,List.map_cons,List.sum_cons,ih (fun k hk => hw k (List.mem_cons_of_mem _ hk))]
    ring

theorem apply_sparse125 (a : ℕ → ℤ) (F : ℕ → ℝ) :
    (∑ i ∈ range 80001, ((sparse125 a i : ℤ) : ℝ)*F i)=∑ j ∈ range 641, (a j : ℝ)*F (125*j) := by
  rw [← sum_sparse125 (fun j => (a j : ℝ)*F (125*j))]
  apply sum_congr rfl
  intro i _
  by_cases h : i%125=0
  · simp only [sparse125,if_pos h,show 125*(i/125)=i by omega]
  · simp [sparse125,h]

theorem apply_totalJump (rows : List SpatialLane) (F : ℕ → ℝ) :
    (∑ i ∈ range 641, (totalJump rows i : ℝ)*F i)=(rows.map (fun v => ∑ i ∈ range 641, (v.jump i : ℝ)*F i)).sum := by
  induction rows with
  | nil => simp [totalJump]
  | cons v rows ih =>
    have H (i : ℕ) : totalJump (v::rows) i=v.jump i+totalJump rows i := rfl
    simp only [H,Int.cast_add,add_mul,sum_add_distrib,List.map_cons,List.sum_cons,ih]

theorem band_tail_difference (w : ℕ) (hw : w≤10000) (f : C(FrequencyInterval,ℝ)) :
    tailTest (40000-4*w) 1 f-tailTest (40000+4*w) 1 f =
      intervalCharge frequencyProjection (-((w : ℝ)/10000)) ((w : ℝ)/10000) f := by
  have H : (w : ℝ)≤10000 := by exact_mod_cast hw
  let a : FrequencyInterval := ⟨-((w : ℝ)/10000),by
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) w]⟩
  let b : FrequencyInterval := ⟨(w : ℝ)/10000,by
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) w]⟩
  have HH := congrArg (fun Q : ContinuousCharge FrequencyInterval => Q f) (interval_as_tails a b)
  simp only [ContinuousLinearMap.sub_apply] at HH
  have hl : ((40000-4*w : ℕ) : ℝ)*1/40000-1 = -((w : ℝ)/10000) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hr : ((40000+4*w : ℕ) : ℝ)*1/40000-1 = (w : ℝ)/10000 := by push_cast; ring
  simpa only [tailTest,Nat.cast_one,hl,hr,a,b] using HH.symm

theorem list_field_sum {A : Type*} (xs : List A) (F : A → ℝ) :
    (xs.map F).sum=∑ j : Fin xs.length, F (xs.get j) := by
  rw [← Fin.sum_ofFn]
  exact (congrArg List.sum (List.map_ofFn.symm.trans (congrArg (List.map F) (List.ofFn_get xs)))).symm

theorem residualJump_zero (rows : List SpatialLane) (ws : List ℕ) (hw : ∀ w∈ws, w≤10000)
    (hd : ∀ v∈rows, v.passes=true) : (∑ i ∈ range 80001, residualJump rows ws i)=0 := by
  have hb := apply_bandJumps ws hw (fun _ => 1)
  have hs := apply_sparse125 (totalJump rows) (fun _ => 1)
  have ht := apply_totalJump rows (fun _ => 1)
  have hz (v : SpatialLane) (hv : v∈rows) : (∑ i ∈ range 641, (v.jump i : ℝ))=0 := by
    exact_mod_cast (v.sound (hd _ hv)).2.1
  simp only [mul_one,sub_self,List.map_const',List.sum_replicate,nsmul_zero,mul_zero] at hb
  simp only [mul_one] at hs ht
  rw [list_field_sum] at ht
  have H : (∑ i ∈ range 80001, (residualJump rows ws i : ℝ))=0 := by
    simp only [residualJump,Int.cast_sub,sum_sub_distrib,hs,ht,hz _ (List.get_mem _ _),
      sum_const_zero,sub_zero]
    exact hb
  exact_mod_cast H

theorem residual_meshReference (s : FourPeriod.Shape) (rows : List SpatialLane)
    (hw : ∀ w∈s.widths, w≤10000) :
    meshReference (n := 80001) (step := 1) (by decide) (residualJump rows s.widths)=
      FourPeriod.fullBandCharge s-∑ j : Fin rows.length,
        meshReference (n := 641) (step := 125) (by decide) (rows.get j).jump := by
  apply ContinuousLinearMap.ext
  intro f
  let F (i : ℕ) := tailTest i 1 f
  have hscale (i : ℕ) : F (125*i)=tailTest i 125 f := by
    unfold F tailTest
    congr 1
    push_cast
    ring
  have he (d : ℕ → ℤ) (n : ℕ) (g : ℕ → ℝ) :
      (∑ i ∈ range n, (d i : ℝ)/100000*g i)=(∑ i ∈ range n, (d i : ℝ)*g i)/100000 := by
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    ring
  simp only [ContinuousLinearMap.sub_apply,FourPeriod.fullBandCharge,ContinuousLinearMap.sum_apply,
    meshReference_apply,he,← sum_div]
  change (∑ i ∈ range 80001, ((residualJump rows s.widths i : ℤ) : ℝ)*F i)/100000=_
  simp only [residualJump,Int.cast_sub,sub_mul,sum_sub_distrib,apply_bandJumps s.widths hw,
    apply_sparse125,apply_totalJump,hscale]
  have hsum : (s.widths.map (fun w => F (40000-4*w)-F (40000+4*w))).sum=
      ∑ j : Fin s.widths.length, intervalCharge frequencyProjection
        (-((s.widths.get j : ℝ)/10000)) ((s.widths.get j : ℝ)/10000) f := by
    rw [list_field_sum]
    exact sum_congr rfl (fun j _ => band_tail_difference _ (hw _ (List.get_mem _ _)) f)
  rw [hsum,list_field_sum rows]
  ring

end PiPolynomialValues
