module

public import OddPiPowers.PolynomialValues.FourPeriod.ColumnKernel

/-! For both accepted lists of shape parameters the complete candidate row
matrix has trivial column kernel at every nonzero complex evaluation point. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def nodesInGroup (groups : List (List ℤ)) (r : Fin 4) : List ℤ := groups[r.val]?.getD []

private theorem four_group_sum (g₀ g₁ g₂ g₃ : List ℤ) (j : ℕ) (f : ℤ → ℕ) :
    (∑ r : Fin 4, (((nodesInGroup [g₀,g₁,g₂,g₃] r).take (j+1)).map f).sum) =
      ((selectedNodes [g₀,g₁,g₂,g₃] j).map f).sum := by
  simp [nodesInGroup, selectedNodes, Fin.sum_univ_succ, List.map_append, List.sum_append,
    Nat.add_assoc]

theorem band_prefix_card (s : Shape) (t : ℕ) (j : Fin s.widths.length) :
    (∑ i : Fin (j.val+1), 2*s.band t (layerBelow j i)) = s.frequencyPrefix (j.val+1) t := by
  have hs : (∑ i : Fin (j.val+1), s.widths.get (layerBelow j i)) = (s.widths.take (j.val+1)).sum := by
    have H := padded_sum_take s.widths id (j.val+1)
    calc
      _ = ∑ i : Fin (j.val+1), if h : i.val < s.widths.length then id s.widths[i.val] else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < s.widths.length := (Nat.le_of_lt_succ i.isLt).trans_lt j.isLt
        rw [dif_pos hi] <;> rfl
      _ = _ := by simpa using H
  calc
    _ = (∑ i : Fin (j.val+1), s.widths.get (layerBelow j i)) * (2*s.rows.sum*t) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      unfold Shape.band
      ring
    _ = _ := by rw [hs]; unfold Shape.frequencyPrefix; ring

private theorem group_nodes_spec {s : Shape} {groups : List (List ℤ)} (h : SignedSchedule s groups)
    (r : Fin 4) (v : ℤ) (hv : v ∈ nodesInGroup groups r) :
    v ≤ (s.ratios.length : ℤ) ∧ v%4 = (r.val : ℤ) := by
  obtain ⟨hmod, hsize⟩ := of_decide_eq_true (List.all_eq_true.mp (h.2.2 r).1 v hv)
  have hbound : (v.natAbs : ℤ) < s.ratios.length := by exact_mod_cast hsize
  rw [Int.natCast_natAbs] at hbound
  exact ⟨(le_abs_self _).trans hbound.le,hmod⟩

private theorem from_certified_nodes {s : Shape} {t : ℕ} {groups : List (List ℤ)}
    (hs : SignedSchedule s groups) (hn : Antitone (s.band t)) (hlen : 0 < s.widths.length)
    (unq : ∀ r : Fin 4, (nodesInGroup groups r).Nodup)
    (room : ∀ j : Fin s.widths.length, s.frequencyPrefix (j.val+1) t <
      ∑ r : Fin 4, (((nodesInGroup groups r).take (j.val+1)).map
        (fun v => scanRowCount s t v-j.val)).sum)
    (y : ℂ) (hy : y ≠ 0) (a : Column (s.band t) → ℂ)
    (rel : ∀ r, ∀ v ∈ nodesInGroup groups r, ∀ σ < scanRowCount s t v,
      ∑ c : Column (s.band t), a c*normalizedEntry v c.2.val σ c.1.val y = 0) : a = 0 := by
  let j₀ : Fin s.widths.length := ⟨0,hlen⟩
  exact trivial_column_kernel_of_contact_room (s.band t) hn (s.band t j₀)
    (fun j => hn (show j₀ ≤ j from Nat.zero_le _)) (nodesInGroup groups) s.ratios.length
    unq (group_nodes_spec hs) (scanRowCount s t)
    (fun j => (band_prefix_card s t j).trans_lt (room j)) y hy a rel

theorem quadratic_candidate_kernel (t : ℕ) (y : ℂ) (hy : y ≠ 0)
    (a : Column (quadraticShape.band t) → ℂ)
    (rel : ∀ r, ∀ v ∈ nodesInGroup quadraticNodeGroups r, ∀ σ < scanRowCount quadraticShape t v,
      ∑ c : Column (quadraticShape.band t), a c*normalizedEntry v c.2.val σ c.1.val y = 0) :
    a = 0 := by
  apply from_certified_nodes quadratic_signed_schedule (quadratic_bands_nested t) (by decide)
    (by unfold nodesInGroup; decide +kernel) _ y hy a rel
  intro j
  rw [show quadraticNodeGroups = [[0],[1,-3],[-2,2],[-1,3]] by rfl, four_group_sum]
  have h := quadratic_contact_room j.isLt t
  change quadraticShape.frequencyPrefix (j.val+1) t < actualContactCount quadraticShape quadraticNodeGroups j.val t
  omega

theorem cubic_candidate_kernel (t : ℕ) (y : ℂ) (hy : y ≠ 0)
    (a : Column (cubicShape.band t) → ℂ)
    (rel : ∀ r, ∀ v ∈ nodesInGroup cubicNodeGroups r, ∀ σ < scanRowCount cubicShape t v,
      ∑ c : Column (cubicShape.band t), a c*normalizedEntry v c.2.val σ c.1.val y = 0) :
    a = 0 := by
  apply from_certified_nodes cubic_signed_schedule (cubic_bands_nested t) (by decide)
    (by unfold nodesInGroup; decide +kernel) _ y hy a rel
  intro j
  rw [show cubicNodeGroups = [[0,-4,4],[1,-3,5],[-2,2,-6,6],[-1,3,-5]] by rfl, four_group_sum]
  have h := cubic_contact_room j.isLt t
  change cubicShape.frequencyPrefix (j.val+1) t < actualContactCount cubicShape cubicNodeGroups j.val t
  omega

end PiPolynomialValues.FourPeriod
