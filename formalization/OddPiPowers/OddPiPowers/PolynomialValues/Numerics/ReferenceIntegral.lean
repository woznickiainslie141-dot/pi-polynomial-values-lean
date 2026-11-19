module

public import OddPiPowers.PolynomialValues.Numerics.CellEnvelope
public import OddPiPowers.PolynomialValues.Numerics.BandQuadrature

/-! Sum the continuous maximum over every layer and cell. The right endpoint
of a priced cell uses the same center as its left endpoint. -/

@[expose] public section

namespace PiPolynomialValues

open Finset

noncomputable def cellValue (rows : List SpatialLane) (hn : 0 < rows.length) (ws : List ℕ)
    (a : AnchorPlan) (price : ℤ) (i : ℕ) : ℝ :=
  let bare := gridCellIntegral (cellField rows hn (fun _ => 0)) i
  if price=0 then (bandCount ws i : ℝ)*bare
  else (bandCount (ws.take 1) i : ℝ)*bare+(bandCount ws.tail i : ℝ)*
    gridCellIntegral (cellField rows hn (fun v => cellFee a price i v.val)) i

theorem bandCount_split (ws : List ℕ) (i : ℕ) :
    bandCount (ws.take 1) i+bandCount ws.tail i=bandCount ws i := by
  cases ws <;> simp [bandCount]

theorem gridCellError_nonneg (rows : List SpatialLane) (i : ℕ) : 0≤gridCellError rows i :=
  sum_nonneg (fun j _ => mul_nonneg (div_nonneg (by exact_mod_cast variationAt_nonneg rows j.val) (by norm_num))
    (cellAllowance_nonneg (by norm_num) _))

theorem weighted_cell_bound (rows : List SpatialLane) (hn : 0 < rows.length) (hd : ∀ v∈rows, v.passes=true)
    (ws : List ℕ) (a : AnchorPlan) (hc : a.covers 0 80000=true) {p : ℤ} (hp : 0≤p) (i : ℕ) (hi : i < 80000) :
    cellValue rows hn ws a p i≤(cellTrap rows ws a p i : ℝ)/(2*40000^2*100000*10^9)+
      (ws.length : ℝ)*(1/40000)*gridCellError rows i := by
  have h (xs : List ℕ) : 0≤(bandCount xs i : ℝ) ∧ (bandCount xs i : ℝ)≤xs.length := by
    exact_mod_cast bandCount_range xs i
  have he := mul_le_mul_of_nonneg_right (h ws).2 (mul_nonneg (by norm_num : 0≤(1:ℝ)/40000)
    (gridCellError_nonneg rows i))
  have H := unpaid_cell_bound rows hn hd i hi
  by_cases hz : p=0
  · have hh := mul_le_mul_of_nonneg_left H (h ws).1
    simp only [cellValue,cellTrap,hz,if_true,Int.cast_mul,Int.cast_add]
    linarith only [hh,he]
  · have H₁ := mul_le_mul_of_nonneg_left H (h (ws.take 1)).1
    have H₂ := mul_le_mul_of_nonneg_left (paid_cell_bound rows hn hd a hc hp i hi) (h ws.tail).1
    have hs : (bandCount (ws.take 1) i : ℝ)+(bandCount ws.tail i : ℝ)=(bandCount ws i : ℝ) := by
      exact_mod_cast bandCount_split ws i
    rw [← hs] at he
    simp only [cellValue,cellTrap,if_neg hz,Int.cast_add,Int.cast_mul]
    linarith only [H₁,H₂,he]

theorem variation_sum (rows : List SpatialLane) :
    (∑ j : Fin 641, (variationAt rows j.val : ℝ)/100000)=(referenceVariation rows : ℝ)/100000 := by
  rw [← sum_div,Fin.sum_univ_eq_sum_range (fun j => (variationAt rows j : ℝ)) 641,
    referenceVariation,packEval_one,Int.cast_sum]

theorem reference_integral_upper (basis : (r : ℕ) → StripeBasis r) (rows : List SpatialLane)
    (hn : 0 < rows.length) (hd : ∀ v∈rows, v.passes=true) (ws : List ℕ) (hw : ws.length≤50)
    (hb : ∀ w∈ws, w≤10000) (a : AnchorPlan) (hc : a.covers 0 80000=true)
    {p : ℤ} (hp : 0≤p) (hbudget : (a.length : ℤ)*|p*400000000000|≤10^27) :
    (∑ i ∈ range 80000, cellValue rows hn ws a p i)≤
      (gridCostBlock 0 125 (fun r => quickReferenceCost rows ws a p r (basis r)) : ℝ)/(2*40000^2*100000*10^9)+
      (ws.length : ℝ)*(referenceVariation rows : ℝ)*22/(4*40000^2*100000) := by
  let B (j : Fin 641) := (variationAt rows j.val : ℝ)/100000
  have hB (j : Fin 641) : 0≤B j := div_nonneg (by exact_mod_cast variationAt_nonneg rows j.val) (by norm_num)
  have H := field_sum_allowance (h := (1:ℝ)/40000) (T := (ws.length : ℝ)) (by norm_num) (by positivity)
    80000 (fun j : Fin 641 => 125*j.val) (fun j => by have := j.isLt; omega) B hB
    (cellValue rows hn ws a p) (fun i => (cellTrap rows ws a p i : ℝ)/(2*40000^2*100000*10^9))
    (fun i hi => weighted_cell_bound rows hn hd ws a hc hp i hi)
  have hlog := mul_le_mul_of_nonneg_left spatial_mesh_log
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) ws.length) (sum_nonneg (s := univ) (fun j _ => hB j)))
  dsimp only [B] at H hlog
  rw [variation_sum] at H hlog
  rw [← sum_div,← Int.cast_sum,← reference_trapezoid basis rows ws a p hd hb hw hbudget] at H
  linarith only [H,hlog]

end PiPolynomialValues
