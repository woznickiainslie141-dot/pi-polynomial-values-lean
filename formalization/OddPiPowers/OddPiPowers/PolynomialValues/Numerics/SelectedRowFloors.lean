module

public import OddPiPowers.PolynomialValues.FourPeriod.SelectedPolynomial
public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxActual

/-! Trimmed-window row floors for every choice of the actual square minor. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset

structure RowData (s : Shape) (g : List (List ℤ)) (K : ℕ) : Prop where
  ratios : (g.flatten.map s.ratioAt).Perm s.rows
  mass_pos : 0 < s.massUnit
  row_pos : ∀ i ∈ s.rows, 0 < s.rowUnits i
  length_pos : 0 < s.rows.length
  pad : s.widths.length+1 ≤ K
  extra : ∀ t, (g.flatten.map (scanRowCount s t)).sum ≤ Fintype.card (Column (s.band t))+K

theorem quadratic_row_data : RowData quadraticShape quadraticNodeGroups 73 := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro t
    rw [quadratic_candidate_excess,shape_column_card]

theorem cubic_row_data : RowData cubicShape cubicNodeGroups 229 := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro t
    rw [cubic_candidate_excess,shape_column_card]

variable {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}

theorem RowData.ratio_mem (D : RowData s g K) (v : Fin g.flatten.length) :
    s.ratioAt (scannedNode g v) ∈ s.rows :=
  D.ratios.mem_iff.mp (List.mem_map.mpr ⟨_,List.get_mem _ v,rfl⟩)

theorem RowData.sum_ratio (D : RowData s g K) (f : ℕ → ℤ) :
    (∑ v, f (s.ratioAt (scannedNode g v))) = (s.rows.map f).sum := by
  rw [← Fin.sum_ofFn]
  have h : List.ofFn (fun v => f (s.ratioAt (scannedNode g v))) =
      (g.flatten.map s.ratioAt).map f := by
    rw [List.map_map]
    change List.ofFn ((f ∘ s.ratioAt) ∘ g.flatten.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [h]
  exact (D.ratios.map f).sum_eq

theorem RowData.selected_count_close (D : RowData s g K) (w : SelectedPolynomial s g t y a b)
    (v : Fin g.flatten.length) :
    |(w.count v : ℝ) - rowRate s (s.ratioAt (scannedNode g v)) * ((s.massUnit*t : ℕ) : ℝ)| ≤ K := by
  let i := s.ratioAt (scannedNode g v)
  have he : scanRowCount s t (scannedNode g v) = s.rowUnits i*t + (s.widths.length+1) := by
    unfold scanRowCount Shape.rowUnits i
    ring
  have hc := w.cap v
  have hd := w.deficit v
  rw [scanned_count_sum] at hd
  have hex := D.extra t
  have hpad := D.pad
  rw [he] at hc hd
  have h₀ : w.count v ≤ s.rowUnits i*t + K := by omega
  have h₁ : s.rowUnits i*t ≤ w.count v + K := by omega
  have hscale : rowRate s i * ((s.massUnit*t : ℕ) : ℝ) = ((s.rowUnits i*t : ℕ) : ℝ) := by
    simp only [rowRate,Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr D.mass_pos.ne']
  change |(w.count v : ℝ) - rowRate s i * _| ≤ _
  rw [hscale,abs_le]
  have e₀ : (w.count v : ℝ) ≤ ((s.rowUnits i*t : ℕ) : ℝ) + K := by exact_mod_cast h₀
  have e₁ : ((s.rowUnits i*t : ℕ) : ℝ) ≤ (w.count v : ℝ) + K := by exact_mod_cast h₁
  constructor <;> linarith

theorem RowData.selected_floor_sum (D : RowData s g K) (w : SelectedPolynomial s g t y a b)
    (l r : Abscissa) (hl : 0 < l.den) (hr : 0 < r.den) (p : ℕ) (hp : 0 < p) (δ : ℝ)
    (hlt : l.value+δ ≤ ((s.massUnit*t : ℕ) : ℝ)/p) (htr : ((s.massUnit*t : ℕ) : ℝ)/p ≤ r.value-δ)
    (hsmall : ∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p) :
    (s.rows.map (rowFloor s l)).sum ≤ ∑ v, ((w.count v/p : ℕ) : ℤ) ∧
    (∑ v, ((w.count v/p : ℕ) : ℤ)) ≤ (s.rows.map (rowStrictUpperFloor s r)).sum := by
  have h (v : Fin g.flatten.length) := actual_row_floor s (s.ratioAt (scannedNode g v)) l r
    D.mass_pos (D.row_pos _ (D.ratio_mem v)) hl hr (w.count v) (s.massUnit*t) p hp K δ hlt htr
    (D.selected_count_close w v) (hsmall _ (D.ratio_mem v))
  rw [← D.sum_ratio (rowFloor s l),← D.sum_ratio (rowStrictUpperFloor s r)]
  exact ⟨sum_le_sum (fun v _ => (h v).1),sum_le_sum (fun v _ => (h v).2)⟩

end PiPolynomialValues.PrimeWindow
