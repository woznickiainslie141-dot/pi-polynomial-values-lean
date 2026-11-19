module

public import OddPiPowers.PolynomialValues.FourPeriod.IndexedContacts
public import OddPiPowers.PolynomialValues.FourPeriod.PaddedNodes
public import OddPiPowers.PolynomialValues.FourPeriod.ColumnTrajectories

/-! A nonzero relation on the actual factorial-normalized rows would produce
too many zeros at the four base points of one nonzero frequency polynomial. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def layerBelow {n : ℕ} (j : Fin n) (i : Fin (j.val+1)) : Fin n :=
  ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt j.isLt⟩

theorem trivial_column_kernel_of_contact_room {n : ℕ} (U : Fin n → ℕ) (hn : Antitone U)
    (top : ℕ) (htop : ∀ j, U j ≤ top) (rows : Fin 4 → List ℤ) (bound : ℕ)
    (huniq : ∀ r, (rows r).Nodup)
    (hnodes : ∀ r, ∀ v ∈ rows r, v ≤ (bound : ℤ) ∧ v%4 = (r.val : ℤ))
    (count : ℤ → ℕ) (hroom : ∀ j : Fin n,
      (∑ i : Fin (j.val+1), 2*U (layerBelow j i)) <
      ∑ r, (((rows r).take (j.val+1)).map (fun v => count v-j.val)).sum)
    (y : ℂ) (hy : y ≠ 0) (a : Column U → ℂ)
    (hrel : ∀ r, ∀ v ∈ rows r, ∀ σ < count v,
      ∑ c : Column U, a c*normalizedEntry v c.2.val σ c.1.val y = 0) : a = 0 := by
  classical
  by_contra ha
  obtain ⟨c,_,hdeg,hp,hd⟩ := exists_top_column U a ha
  let j : Fin n := c.1
  let S := Finset.Icc (-(top : ℤ)) (top : ℤ)
  have hS (k : Fin n) : Finset.Icc (-(U k : ℤ)) (U k : ℤ) ⊆ S := by
    intro t ht
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp ht
    have hu := htop k
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hl (t : ℤ) (ht : t ∈ S) : 0 ≤ t+(top : ℤ) := by
    have h := (Finset.mem_Icc.mp ht).1
    omega
  let ord (r : Fin 4) (i : Fin (j.val+1)) :=
    if hi : i.val < (rows r).length then count (rows r)[i.val] else 0
  let node (r : Fin 4) (i : Fin (j.val+1)) := paddedNode (rows r) bound i.val
  let shift (r : Fin 4) (i : Fin (j.val+1)) := ((node r i : ℤ) : ℂ)*Complex.I*y/2
  have hinj (r : Fin 4) : Function.Injective (shift r) := by
    apply node_shift_injective hy
    exact (paddedNode_injective (hn := huniq r) (hb := fun v hv => (hnodes r v hv).1)).comp
      Fin.val_injective
  have hv (r : Fin 4) (i : Fin (j.val+1)) :
      (PowerSeries.X : PowerSeries ℂ)^(ord r i) ∣
        translatedTrajectory (fourthBase r) (shift r i) S (columnPolynomial U a) := by
    by_cases hi : i.val < (rows r).length
    · have hm := List.getElem_mem hi
      have hv := translatedTrajectory_prefix_dvd U a S hS (rows r)[i.val] y
        (count (rows r)[i.val]) (hrel r _ hm)
      rw [node_base_eq (hnodes r _ hm).2] at hv
      simpa only [ord, shift, node, paddedNode, dif_pos hi] using hv
    · simp [ord,hi]
  have H := indexed_contact_sum_le_band S (columnPolynomial U a) top
    (fun i : Fin (j.val+1) => U (layerBelow j i)) (fun i => htop _)
    (fun i => columnPolynomial_inBand U hn a S (layerBelow j i)) hl (fun t _ => hd t)
    (hS c.1 c.2.property) hp hdeg fourthBase fourthBase_injective fourthBase_ne_zero
    shift hinj ord hv
  have hsum (r : Fin 4) : ∑ i : Fin (j.val+1), (ord r i - j.val) =
      (((rows r).take (j.val+1)).map (fun v => count v-j.val)).sum := by
    calc
      _ = ∑ i : Fin (j.val+1), if h : i.val < (rows r).length
            then count (rows r)[i.val]-j.val else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.val < (rows r).length <;> simp [ord,hi]
      _ = _ := padded_sum_take (rows r) (fun v => count v-j.val) (j.val+1)
  simp_rw [hsum] at H
  exact (not_lt_of_ge H) (hroom j)

end PiPolynomialValues.FourPeriod
