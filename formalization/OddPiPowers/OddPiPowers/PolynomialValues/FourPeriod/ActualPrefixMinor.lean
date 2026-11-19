module

public import OddPiPowers.PolynomialValues.FourPeriod.ActualSelectionRank
public import OddPiPowers.PolynomialValues.FourPeriod.PrefixMinor

/-! An actual interpolating minor at each exact integer scale for both
designs. Only a nonzero specialization point is required. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def scannedNode (groups : List (List ℤ)) (i : Fin groups.flatten.length) : ℤ := groups.flatten.get i

theorem groupNode_scanned {groups : List (List ℤ)} (hg : groups.length = 4) (r : Fin 4)
    (v : ℤ) (hv : v ∈ nodesInGroup groups r) : ∃ i, scannedNode groups i = v := by
  have hr : r.val < groups.length := by rw [hg]; exact r.isLt
  have he : v ∈ groups[r.val] := by
    simpa only [nodesInGroup, List.getElem?_eq_getElem hr, Option.getD_some] using hv
  have hf : v ∈ groups.flatten := List.mem_flatten.mpr ⟨groups[r.val],List.getElem_mem hr,he⟩
  exact List.mem_iff_get.mp hf

def ShapeHasPrefixMinor (s : Shape) (groups : List (List ℤ)) (t : ℕ) (y : ℂ) : Prop :=
  HasPrefixMinor (fun i => scanRowCount s t (scannedNode groups i)) (scannedNode groups)
    (columnLabel (U := s.band t)) y

private theorem shapeMinor_of_kernel {s : Shape} {groups : List (List ℤ)} {t : ℕ} {y : ℂ}
    (hg : groups.length = 4) (hn : Antitone (s.band t))
    (hker : ∀ a : Column (s.band t) → ℂ, (∀ r, ∀ v ∈ nodesInGroup groups r,
      ∀ σ < scanRowCount s t v, ∑ c : Column (s.band t),
        a c*normalizedEntry v c.2.val σ c.1.val y = 0) → a = 0) :
    ShapeHasPrefixMinor s groups t y := by
  let count (i : Fin groups.flatten.length) := scanRowCount s t (scannedNode groups i)
  let H := ∑ i, count i
  have hc (i) : count i ≤ H := Finset.single_le_sum (f := count) (s := Finset.univ)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  apply prefixMinor_of_candidate_kernel count H hc (scannedNode groups) columnLabel
    (previousColumn hn) (previousColumn_label hn) y
  intro a h
  apply hker a
  intro r v hv
  obtain ⟨i,rfl⟩ := groupNode_scanned hg r v hv
  exact h i

theorem quadratic_actual_prefix_minor (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeHasPrefixMinor quadraticShape quadraticNodeGroups t y :=
  shapeMinor_of_kernel (by decide) (quadratic_bands_nested t) (quadratic_candidate_kernel t y hy)

theorem cubic_actual_prefix_minor (t : ℕ) {y : ℂ} (hy : y ≠ 0) :
    ShapeHasPrefixMinor cubicShape cubicNodeGroups t y :=
  shapeMinor_of_kernel (by decide) (cubic_bands_nested t) (cubic_candidate_kernel t y hy)

end PiPolynomialValues.FourPeriod
