module

public import OddPiPowers.PolynomialValues.Numerics.PrimeShapeData
public import OddPiPowers.PolynomialValues.FourPeriod.PositivePrimeBudget

/-! At each actual prime, the finite-level cancellations dominate the
certified signed ramps, up to the fixed row-padding error per level. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

private theorem real_nat_sub (m a : ℕ) : ((m-a : ℕ) : ℝ) = max 0 ((m : ℝ)-a) := by
  rcases le_total a m with h|h
  · rw [Nat.cast_sub h,max_eq_right (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero,max_eq_left (sub_nonpos.mpr (by exact_mod_cast h))]

private theorem scale_ramp (N p : ℕ) (hN : 0 < N) (e : TailTerm) (h : ℕ) :
    (N : ℝ)*e.value h ((p : ℝ)/N) =
      max 0 ((N : ℝ)*(e.width : ℝ) - ((h-e.grade : ℕ) : ℝ)*p) := by
  rw [TailTerm.value,mul_max_of_nonneg _ _ (Nat.cast_nonneg N),mul_zero]
  congr 1
  field_simp [Nat.cast_ne_zero.mpr hN.ne'] <;> ring

variable {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}

theorem PrimeShapeData.column_ramp_le (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b)
    (ht : 0 < t) (p h : ℕ) (hp : 0 < p) :
    let N := s.massUnit*t
    4*(N : ℝ)*listTail s.columnTails h ((p : ℝ)/N) ≤ columnLevelCount w.colIndex p h := by
  let N := s.massUnit*t
  have hN : 0 < N := Nat.mul_pos D.mass_pos ht
  change 4*(N : ℝ)*listTail _ _ _ ≤ _
  rw [← D.column_sum,columnLevelCount_eq _ p h hp,Nat.cast_sum,mul_sum]
  apply sum_le_sum
  intro j _
  rw [mul_assoc,scale_ramp N p hN,mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4),mul_zero,
    real_nat_sub (2*s.band t j+1) (4*((h-j.val)*p))]
  apply max_le_max_left
  have he : 4*((N : ℝ)*((columnTerm s j).width : ℝ)) = 2*(s.band t j : ℝ) := by
    simp only [columnTerm,TailTerm.width,Rat.cast_div,Rat.cast_natCast,N,Shape.massUnit,Shape.band,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  change 4*((N : ℝ)*((columnTerm s j).width : ℝ)-((h-j.val : ℕ) : ℝ)*p) ≤ _
  push_cast
  linarith only [he]

theorem PrimeShapeData.row_ramp_ge (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b)
    (ht : 0 < t) (p h : ℕ) (hp : 0 < p) :
    let N := s.massUnit*t
    (rowLevelCount w.rows p h : ℝ) ≤ (N : ℝ)*listTail s.rowTails h ((p : ℝ)/N) +
      g.flatten.length*(s.widths.length+1 : ℕ) := by
  let N := s.massUnit*t
  have hN : 0 < N := Nat.mul_pos D.mass_pos ht
  have hr := actual_row_tail w.rowIndex (scannedNode g) (scannedRank g) D.rank_inj p h hp
  have hr' : (rowLevelCount w.rows p h : ℝ) ≤ ∑ v, ((w.count v - (h-scannedRank g v)*p : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hr
  apply hr'.trans
  change _ ≤ (N : ℝ)*listTail _ _ _ + _
  rw [← D.row_sum,mul_sum]
  have hc : (∑ _v : Fin g.flatten.length, ((s.widths.length+1 : ℕ) : ℝ)) =
      (g.flatten.length : ℝ)*((s.widths.length+1 : ℕ) : ℝ) := by
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← hc,← sum_add_distrib]
  apply sum_le_sum
  intro v _
  rw [real_nat_sub,scale_ramp N p hN]
  have he : (N : ℝ)*((nodeTerm s g v).width : ℝ) =
      ((s.rowUnits (s.ratioAt (scannedNode g v))*t : ℕ) : ℝ) := by
    simp only [nodeTerm,TailTerm.width,Rat.cast_div,Rat.cast_natCast,N,Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr D.mass_pos.ne'] <;> ring
  rw [he]
  let z := (s.rowUnits (s.ratioAt (scannedNode g v))*t : ℕ)
  have hcap : w.count v ≤ z+(s.widths.length+1) := by
    apply (w.cap v).trans_eq
    unfold scanRowCount z Shape.rowUnits
    ring
  let loss : ℝ := ((h-scannedRank g v : ℕ) : ℝ)*p
  have hcap' : (w.count v : ℝ) ≤ (z : ℝ)+((s.widths.length+1 : ℕ) : ℝ) := by exact_mod_cast hcap
  rw [Nat.cast_mul (h-scannedRank g v) p]
  change max 0 ((w.count v : ℝ)-loss) ≤ max 0 ((z : ℝ)-loss)+((s.widths.length+1 : ℕ) : ℝ)
  apply max_le
  · positivity
  · linarith only [hcap',le_max_right (0 : ℝ) ((z : ℝ)-loss)]

theorem PrimeShapeData.net_ramp_le (D : PrimeShapeData s g K) (w : SelectedPolynomial s g t y a b)
    (ht : 0 < t) (p h : ℕ) (hp : 0 < p) :
    let N := s.massUnit*t
    (N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue h ((p : ℝ)/N) ≤
      (columnLevelCount w.colIndex p h : ℝ) - rowLevelCount w.rows p h +
      (g.flatten.length : ℝ)*((s.widths.length+1 : ℕ) : ℝ) := by
  let N := s.massUnit*t
  have hc := D.column_ramp_le w ht p h hp
  have hr := D.row_ramp_ge w ht p h hp
  have hw : 0 < (s.totalWidthQ : ℝ) := by
    have hq : 0 < s.totalWidthQ := div_pos (mul_pos (by norm_num) (by exact_mod_cast D.widths_pos)) (by norm_num)
    exact_mod_cast hq
  change (N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue h ((p : ℝ)/N) ≤ _
  calc
    _ = (N : ℝ)*(4*listTail s.columnTails h ((p : ℝ)/N)-listTail s.rowTails h ((p : ℝ)/N)) := by
      unfold Shape.netTailValue
      field_simp [hw.ne']
    _ ≤ _ := by dsimp only [N] at *; linarith only [hc,hr]

end PiPolynomialValues.FourPeriod
