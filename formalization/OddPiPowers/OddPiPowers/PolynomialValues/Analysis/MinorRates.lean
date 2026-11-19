module

public import OddPiPowers.PolynomialValues.Analysis.AngularDeterminant
public import OddPiPowers.PolynomialValues.Analysis.TaylorLabelCosts

/-! Normalized interior estimates retain the individual Taylor labels.
The row order is counted once for the selected determinant, independent
of the permutation realizing the boundary estimate. -/

@[expose] public section

namespace PiPolynomialValues.SelectedSequence

open FourPeriod Finset Filter Real

variable {P : EvaluationPlan} (W : SelectedSequence P)

def order (i : ℕ) := ∑ j, ((W.witness i).rowIndex j).2.val

noncomputable def markCount (i : ℕ) (h : LabelChoice (W.layer i)) : ℝ :=
  ∑ j, if (h j).val=0 then 0 else 1

noncomputable def totalLabel (i : ℕ) (h : LabelChoice (W.layer i)) : ℝ := ∑ j, ((h j).val : ℝ)

def minorRate (r E fee : ℝ) : Prop := ∀ ε>0, ∀ᶠ i in atTop, ∀ h : LabelChoice (W.layer i),
  ∃ q : LabelChoice (fun c => (h c).val),
    ‖W.minor i h (fun u => phasePoint (scannedNode P.groups u))‖≤exp
      ((W.mass i)^2*((P.rates.length : ℝ)*E+ε)-W.mass i*W.markCount i h*fee+
        ((W.order i : ℝ)-labelPairs (fun c => (q c).val))*log (1/r))

theorem order_upper : UpperRate atTop (fun i => (W.order i : ℝ)/(W.mass i)^2)
    ((P.rates.length : ℝ)*P.rates.rowSquare) := by
  have H := normalized_rowOrder_upper P.rows W.index_atTop W.witness
  rw [P.square] at H
  have he : ((2*P.rates.length*P.rates.rowSquare : ℚ) : ℝ)/2=
      (P.rates.length : ℝ)*P.rates.rowSquare := by push_cast; ring
  rw [he] at H
  exact H

theorem markCount_bounds (i : ℕ) (h : LabelChoice (W.layer i)) : 0≤W.markCount i h ∧ W.markCount i h≤W.size i := by
  constructor
  · exact sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  · simpa only [markCount,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      sum_le_sum (s := univ) (f := fun j => if (h j).val=0 then (0 : ℝ) else 1)
      (g := fun _ => (1 : ℝ)) (fun j _ => by split_ifs <;> norm_num)

theorem totalLabel_bounds (i : ℕ) (h : LabelChoice (W.layer i)) :
    0≤W.totalLabel i h ∧ W.totalLabel i h≤(W.size i : ℝ)*P.shape.widths.length := by
  refine ⟨sum_nonneg (fun _ _ => Nat.cast_nonneg _),?_⟩
  have H (c : Fin (W.size i)) : (h c).val≤P.shape.widths.length :=
    (Nat.lt_succ_iff.mp (h c).isLt).trans ((W.witness i).colIndex c).1.isLt.le
  simpa only [totalLabel,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
    sum_le_sum (s := univ) (fun c _ => (Nat.cast_le (α := ℝ)).mpr (H c))

theorem small_label_pairs {n J : ℕ} (j : Fin n → ℕ) (hj : ∀ c, j c≤J)
    (h : LabelChoice j) (q : LabelChoice (fun c => (h c).val)) :
    0≤(labelPairs (fun c => (q c).val) : ℝ) ∧
    2*(labelPairs (fun c => (q c).val) : ℝ)≤(n : ℝ)^2 := by
  let a (i : Fin n) : Fin (J+2) := ⟨(q i).val,by
    have h₁ : (q i).val < (h i).val+1 := (q i).isLt
    have h₂ := (h i).isLt
    have h₃ := hj i
    omega⟩
  have hs : (∑ u, (finiteLabelCount a u : ℝ))=(n : ℝ) := by rw [← Nat.cast_sum,finiteLabelCount_sum]
  have hle (u : Fin (J+2)) : (finiteLabelCount a u : ℝ)≤n :=
    (single_le_sum (fun k _ => Nat.cast_nonneg (α := ℝ) (finiteLabelCount a k)) (mem_univ u)).trans_eq hs
  have H := sum_le_sum (s := univ) (fun u _ => mul_le_mul_of_nonneg_left (hle u)
    (Nat.cast_nonneg (α := ℝ) (finiteLabelCount a u)))
  simp only [← sq,← sum_mul,hs,finiteLabelCount_squares] at H
  refine ⟨Nat.cast_nonneg _,?_⟩
  change 2*(labelPairs (fun c => (q c).val) : ℝ)+(n : ℝ)≤(n : ℝ)^2 at H
  nlinarith only [H,Nat.cast_nonneg (α := ℝ) n]

end PiPolynomialValues.SelectedSequence
