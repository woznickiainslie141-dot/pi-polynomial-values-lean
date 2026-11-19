module

public import OddPiPowers.PolynomialValues.Analysis.SelectedScaleLimits
public import OddPiPowers.PolynomialValues.Analysis.ReferenceEnergyCost
public import OddPiPowers.PolynomialValues.UpperRates

/-! Sum the factorial bounds over the actual selected rows. The same row
masses control the row-order term lost when a zero at the origin is used. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Real Filter Finset PrimeWindow
open scoped Topology

def scannedSquareQ (s : Shape) (g : List (List ℤ)) : ℚ :=
  ∑ j : Fin g.flatten.length, (s.rowMassQ (s.ratioAt (scannedNode g j)))^2

theorem quadratic_scanned_square : scannedSquareQ quadraticShape quadraticNodeGroups=
    2*quadraticRateData.length*quadraticRateData.rowSquare := by decide +kernel

theorem cubic_scanned_square : scannedSquareQ cubicShape cubicNodeGroups=
    2*cubicRateData.length*cubicRateData.rowSquare := by decide +kernel

theorem selected_count_positive {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape} {g : List (List ℤ)}
    {K a b : ℕ} {y : ι → ℂ} (D : RowData s g K) (ht : Tendsto t F atTop)
    (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) :
    ∀ᶠ i in F, ∀ v, 0<(w i).count v ∧ (w i).count v≤Fintype.card (Column (s.band (t i))) := by
  apply eventually_all.mpr
  intro v
  have hR : 0 < rowRate s (s.ratioAt (scannedNode g v)) := div_pos
    (by exact_mod_cast D.row_pos _ (D.ratio_mem v)) (by exact_mod_cast D.mass_pos)
  filter_upwards [(selected_mass_limit D ht w v).eventually (lt_mem_nhds hR)] with i hi
  constructor
  · by_contra! h
    have hz : (w i).count v=0 := Nat.eq_zero_of_le_zero h
    simp [hz] at hi
  · exact (single_le_sum (fun j _ => Nat.zero_le ((w i).count j)) (mem_univ v)).trans_eq (w i).total

noncomputable def scannedBlockLimit (s : Shape) (g : List (List ℤ)) (r : ℝ) :=
  ∑ v : Fin g.flatten.length, let A := rowRate s (s.ratioAt (scannedNode g v))
    A^2/2*(3/2-log (2*A)+log (1/r))

theorem selected_blocks_limit {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape} {g : List (List ℤ)}
    {K a b : ℕ} {y : ι → ℂ} (D : RowData s g K) (ht : Tendsto t F atTop)
    (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) {r : ℝ} (hr : 0<r) :
    Tendsto (fun i => ∑ v, blockScaleCost ((s.massUnit*t i : ℕ) : ℝ) r ((w i).count v)) F
      (𝓝 (scannedBlockLimit s g r)) := by
  apply tendsto_finsetSum
  intro v _
  exact blockScaleCost_limit (massScale_atTop ht D.mass_pos) (selected_mass_limit D ht w v)
    (div_pos (by exact_mod_cast D.row_pos _ (D.ratio_mem v)) (by exact_mod_cast D.mass_pos)) (fun _ => Nat.cast_nonneg _) hr

theorem scannedBlock_outer (s : Shape) (g : List (List ℤ)) (S : ScanOrder s g) :
    Tendsto (fun k => scannedBlockLimit s g (innerRadius k)) atTop (𝓝 (analyticBaseSum s.massList/2)) := by
  have hR : Tendsto (fun k => log (1/innerRadius k)) atTop (𝓝 0) := by
    have hI : Tendsto (fun k => 1/innerRadius k) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Pi.div_def,div_one] using
        (tendsto_const_nhds (x := (1 : ℝ))).div innerRadius_tendsto (by norm_num : (1 : ℝ)≠0)
    simpa only [Function.comp_def,Real.log_one] using (continuousAt_log (by norm_num : (1 : ℝ)≠0)).tendsto.comp hI
  let A (j : Fin s.rows.length) := (s.rowMassQ (s.rows.get j) : ℝ)
  have h (v : Fin g.flatten.length) : rowRate s (s.ratioAt (scannedNode g v))=A (S.rank v) := by
    rw [S.ratio]; simp only [rowRate,A,Shape.rowMassQ,Rat.cast_div,Rat.cast_natCast]
  have H := tendsto_finsetSum (univ : Finset (Fin g.flatten.length)) (fun v _ =>
    (hR.const_add (3/2-log (2*A (S.rank v)))).const_mul (A (S.rank v)^2/2))
  simp only [add_zero] at H
  have he := S.rank.sum_comp (fun j => A j^2/2*(3/2-log (2*A j)))
  rw [he] at H
  have ha : (∑ j : Fin s.rows.length, A j^2/2*(3/2-log (2*A j)))=analyticBaseSum s.massList/2 := by
    let f (j : ℕ) := (s.rowMassQ j : ℝ)^2*(3/2-log (2*(s.rowMassQ j : ℝ)))
    have he (l : List ℕ) : analyticBaseSum (l.map s.rowMassQ)=(l.map f).sum := by
      induction l with
      | nil => rfl
      | cons j l ih => exact congrArg (fun x : ℝ => f j+x) ih
    rw [Shape.massList,he,list_field_sum,sum_div]
    apply sum_congr rfl
    intro j _
    dsimp only [A,f]
    ring
  rw [ha] at H
  simpa only [scannedBlockLimit,h] using H

theorem twice_fin_indices (n : ℕ) : 2*(∑ i : Fin n, (i.val : ℝ))+(n : ℝ)=(n : ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_succ]
    linarith only [ih]

theorem rowOrder_square_upper {n V : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m) :
    ((∑ i, (e i).2.val : ℕ) : ℝ)≤(∑ u, (m u : ℝ)^2)/2 := by
  rw [Nat.cast_sum,e.sum_comp (fun i : RowCandidates m => (i.2.val : ℝ)),Fintype.sum_sigma,sum_div]
  exact sum_le_sum (fun v _ => by linarith only [twice_fin_indices (m v),Nat.cast_nonneg (α := ℝ) (m v)])

theorem normalized_rowOrder_upper {ι : Type*} {F : Filter ι} {t : ι → ℕ} {s : Shape} {g : List (List ℤ)}
    {K a b : ℕ} {y : ι → ℂ} (D : RowData s g K) (ht : Tendsto t F atTop)
    (w : ∀ i, SelectedPolynomial s g (t i) (y i) a b) :
    UpperRate F (fun i => ((∑ j, ((w i).rowIndex j).2.val : ℕ) : ℝ)/((s.massUnit*t i : ℕ) : ℝ)^2)
      ((scannedSquareQ s g : ℝ)/2) := by
  have h := (tendsto_finsetSum univ (fun v _ => (selected_mass_limit D ht w v).pow 2)).div_const 2
  have h' := UpperRate.of_tendsto h
  have hle (i : ι) : ((∑ j, ((w i).rowIndex j).2.val : ℕ) : ℝ)/((s.massUnit*t i : ℕ) : ℝ)^2≤
      (∑ v, (((w i).count v : ℝ)/((s.massUnit*t i : ℕ) : ℝ))^2)/2 := by
    have he := div_le_div_of_nonneg_right (rowOrder_square_upper (w i).rowIndex) (sq_nonneg ((s.massUnit*t i : ℕ) : ℝ))
    apply he.trans_eq
    simp only [div_pow,← sum_div]
    ring
  exact h'.mono (Eventually.of_forall hle) (by
    simp only [scannedSquareQ,Rat.cast_sum,Rat.cast_pow,Shape.rowMassQ,Rat.cast_div,Rat.cast_natCast,rowRate,le_refl])

end PiPolynomialValues.FourPeriod
