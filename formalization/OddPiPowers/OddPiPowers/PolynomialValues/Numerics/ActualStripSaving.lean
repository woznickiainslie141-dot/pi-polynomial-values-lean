module

public import OddPiPowers.PolynomialValues.Numerics.SelectedRowFloors
public import OddPiPowers.PolynomialValues.Numerics.ActualBandInventory
public import OddPiPowers.PolynomialValues.Numerics.FoldedResidueLattice

/-! Apply the checked open trapezoids on a trimmed window directly to the
prime valuation of the denominator of the selected integer polynomial. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset

private theorem map_sum_mono {α : Type*} (xs : List α) (f h : α → ℤ) (le : ∀ i, f i ≤ h i) :
    (xs.map f).sum ≤ (xs.map h).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact add_le_add (le x) ih

variable {s : Shape} {g : List (List ℤ)} {K t a b : ℕ} {y : ℂ}

theorem selected_folded_inventory (w : SelectedPolynomial s g t y a b)
    {p : ℕ} (hp : 0 < p) (r : Fin p) :
    (residueMultiplicity hp (fun i => (w.cols i).1) r : ℤ) =
      (s.widths.map (fun u => bandCount u (((s.massUnit*t : ℕ) : ℝ)/p) ((foldedIndex r : ℝ)/p))).sum := by
  unfold SelectedPolynomial.cols
  rw [actual_column_inventory s t w.colIndex hp r]
  by_cases he : r.val ≤ p-r.val
  · simp only [foldedIndex,min_eq_left he]
  · have he' : ((foldedIndex r : ℕ) : ℝ)/p = 1-(r.val : ℝ)/p := by
      simp only [foldedIndex,min_eq_right (by omega : p-r.val ≤ r.val),Nat.cast_sub r.isLt.le]
      field_simp [Nat.cast_ne_zero.mpr hp.ne']
    rw [he']
    simp only [bandCount_reflect]

theorem on_strip_excess (D : RowData s g K) (w : SelectedPolynomial s g t y a b)
    (l u : Abscissa) (hl : 0 < l.den) (hu : 0 < u.den) (p : ℕ) (hp : 0 < p)
    (δ : ℝ) (hδ : 0 ≤ δ) (hlo : l.value+δ ≤ ((s.massUnit*t : ℕ) : ℝ)/p)
    (hhi : ((s.massUnit*t : ℕ) : ℝ)/p ≤ u.value-δ)
    (hsmall : ∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p)
    (z : Box) (r : Fin p)
    (hbot : z.bottom.value (((s.massUnit*t : ℕ) : ℝ)/p) < (foldedIndex r : ℝ)/p)
    (htop : (foldedIndex r : ℝ)/p < z.top.value (((s.massUnit*t : ℕ) : ℝ)/p)) :
    let x := (residueMultiplicity hp (fun i => (w.cols i).1) r : ℤ) - ∑ v, ((w.count v/p : ℕ) : ℤ)
    lowerExcess s l u z ≤ x ∧ x ≤ upperExcess s l u z := by
  dsimp only
  rw [selected_folded_inventory w hp r]
  have hf := D.selected_floor_sum w l u hl hu p hp δ hlo hhi hsmall
  have h₀ : l.value ≤ ((s.massUnit*t : ℕ) : ℝ)/p := by linarith
  have h₁ : ((s.massUnit*t : ℕ) : ℝ)/p ≤ u.value := by linarith
  have hc (j : ℕ) := band_count_between l u z j hl hu h₀ h₁ hbot htop
  exact ⟨sub_le_sub (map_sum_mono _ _ _ (fun j => (hc j).1)) hf.2,
    sub_le_sub (map_sum_mono _ _ _ (fun j => (hc j).2)) hf.1⟩

theorem checked_lattice_surplus (D : RowData s g K) (w : SelectedPolynomial s g t y a b)
    (l u : Abscissa) (hl : 0 < l.den) (hu : 0 < u.den) (p : ℕ) (hp : 0 < p)
    (δ : ℝ) (hδ : 0 ≤ δ) (hlo : l.value+δ ≤ ((s.massUnit*t : ℕ) : ℝ)/p)
    (hhi : ((s.massUnit*t : ℕ) : ℝ)/p ≤ u.value-δ)
    (hsmall : ∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p)
    (bs : List Box) (hbs : boxesPass s l u ⟨0,0⟩ bs = true) :
    2*(latticeSaving bs (s.massUnit*t) p : ℤ) ≤ residueSurplus w.count w.cols hp := by
  let x (r : Fin p) := (residueMultiplicity hp (fun i => (w.cols i).1) r : ℤ) -
    ∑ v, ((w.count v/p : ℕ) : ℤ)
  let N := s.massUnit*t
  have hord := checked_strips s l u hl hu (t := (N : ℝ)/p) (by dsimp [N]; linarith)
    (by dsimp [N]; linarith) ⟨0,0⟩ bs hbs
  have hlgt : g.flatten.length = s.rows.length := by simpa only [List.length_map] using D.ratios.length_eq
  apply (sum_folded_gains bs N p hp ⟨0,0⟩ (by simp [Boundary.value]) hord.1).trans
  unfold residueSurplus
  apply sum_le_sum
  intro r _
  change stripGains ((N : ℝ)/p) ((foldedIndex r : ℝ)/p) bs ≤ collisionTwice (x r) (g.flatten.length : ℤ)
  rw [show (g.flatten.length : ℤ) = (s.rows.length : ℤ) from congrArg Nat.cast hlgt]
  apply stripGains_le _ _ _ _ hord.1 (collisionTwice_nonneg _ _ (by exact_mod_cast D.length_pos))
  intro z hz hb ht
  exact certified_gain_of_bounds s l u z D.length_pos
    (on_strip_excess D w l u hl hu p hp δ hδ hlo hhi hsmall z r hb ht) (hord.2 z hz).1

theorem selected_strip_prime_cost (D : RowData s g K) (w : SelectedPolynomial s g t y a b)
    (l u : Abscissa) (hl : 0 < l.den) (hu : 0 < u.den) (p : ℕ) (hp : p.Prime)
    (δ : ℝ) (hδ : 0 ≤ δ) (hlo : l.value+δ ≤ ((s.massUnit*t : ℕ) : ℝ)/p)
    (hhi : ((s.massUnit*t : ℕ) : ℝ)/p ≤ u.value-δ)
    (hsmall : ∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p) (hm : ∀ v, w.count v ≤ p^2)
    (bs : List Box) (hbs : boxesPass s l u ⟨0,0⟩ bs = true) :
    w.denominator.factorization p ≤ (∑ j, (w.cols j).2) - nodePairOrder (scannedNode g) w.count -
      latticeSaving bs (s.massUnit*t) p :=
  w.residue_cost p _ hp hm (checked_lattice_surplus D w l u hl hu p hp.pos δ hδ hlo hhi hsmall bs hbs)

end PiPolynomialValues.PrimeWindow
