module

public import OddPiPowers.PolynomialValues.FourPeriod.GreedyBasis
public import Mathlib.Order.Interval.Finset.Fin

/-! The greedy basis consists of full prefixes, including empty prefixes.
Its total size is exactly the number of actual columns. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

noncomputable def keptAt {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ) (row : Fin V → ℕ → κ → ℂ)
    (v : Fin V) : Finset (Fin (count v)) := by
  classical
  exact Finset.univ.filter fun i => rowKept delay row v i.val

noncomputable def prefixSize {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ) (row : Fin V → ℕ → κ → ℂ)
    (v : Fin V) : ℕ := (keptAt count delay row v).card

theorem prefixSize_le {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (v : Fin V) : prefixSize count delay row v ≤ count v := by
  simpa [prefixSize] using (keptAt count delay row v).card_le_univ

theorem kept_iff_lt_size {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ) (row : Fin V → ℕ → κ → ℂ)
    (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ)) (hT : ∀ v k, T (row v k) = row v (k+1))
    (v : Fin V) (i : Fin (count v)) :
    rowKept delay row v i.val ↔ i.val < prefixSize count delay row v := by
  classical
  let S := keptAt count delay row v
  have hm (k : Fin (count v)) : k ∈ S ↔ rowKept delay row v k.val := by
    simp [S,keptAt]
  constructor
  · intro h
    have hs : Finset.Iic i ⊆ S := fun k hk =>
      (hm k).mpr (rowKept_initial_segment delay row T hT v (show k ≤ i from Finset.mem_Iic.mp hk) h)
    have hcard := Finset.card_le_card hs
    rw [Fin.card_Iic] at hcard
    exact hcard
  · intro h
    by_contra hn
    have hs : S ⊆ Finset.Iio i := by
      intro k hk
      apply Finset.mem_Iio.mpr
      by_contra he
      exact hn (rowKept_initial_segment delay row T hT v (le_of_not_gt he) ((hm k).mp hk))
    have hcard := Finset.card_le_card hs
    rw [Fin.card_Iio] at hcard
    exact (not_lt_of_ge hcard) h

noncomputable def chosenPrefixEquiv {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ))
    (hT : ∀ v k, T (row v k) = row v (k+1)) :
    ↥(chosenCandidates count delay row) ≃ RowCandidates (prefixSize count delay row) where
  toFun c := by
    classical
    exact ⟨c.val.1,c.val.2.val,(kept_iff_lt_size count delay row T hT _ _).mp
      (Finset.mem_filter.mp c.property).2⟩
  invFun c := by
    classical
    let k : Fin (count c.1) := ⟨c.2.val,c.2.isLt.trans_le (prefixSize_le count delay row _)⟩
    exact ⟨⟨c.1,k⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (kept_iff_lt_size count delay row T hT _ k).mpr c.2.isLt⟩⟩
  left_inv := by rintro ⟨⟨v,k⟩,h⟩; rfl
  right_inv := by rintro ⟨v,k⟩; rfl

noncomputable def prefixRowBasis {V : ℕ} {κ : Type*} [Fintype κ] (count : Fin V → ℕ)
    (H : ℕ) (hH : ∀ v, count v ≤ H) (row : Fin V → ℕ → κ → ℂ)
    (hk : ∀ a : κ → ℂ, (∀ c : RowCandidates count, ∑ j, a j * row c.1 c.2.val j = 0) → a = 0) :
    Module.Basis ↥(chosenCandidates count (fun v => H-count v) row) ℂ (κ → ℂ) :=
  Module.Basis.mk (chosenCandidates_independent count _ row) (by
    rw [chosenCandidates_span count H hH row,
      span_of_trivial_candidate_kernel (fun c : RowCandidates count => row c.1 c.2.val) hk])

theorem prefixSize_sum {V : ℕ} {κ : Type*} [Fintype κ] (count : Fin V → ℕ)
    (H : ℕ) (hH : ∀ v, count v ≤ H) (row : Fin V → ℕ → κ → ℂ)
    (hk : ∀ a : κ → ℂ, (∀ c : RowCandidates count, ∑ j, a j * row c.1 c.2.val j = 0) → a = 0)
    (T : (κ → ℂ) →ₗ[ℂ] (κ → ℂ)) (hT : ∀ v k, T (row v k) = row v (k+1)) :
    ∑ v, prefixSize count (fun v => H-count v) row v = Fintype.card κ := by
  classical
  let E := chosenPrefixEquiv count (fun v => H-count v) row T hT
  have hb := Module.finrank_eq_card_basis (prefixRowBasis count H hH row hk)
  rw [Module.finrank_fintype_fun_eq_card] at hb
  have he := Fintype.card_congr E
  rw [Fintype.card_sigma] at he
  simp only [Fintype.card_fin] at he
  exact he.symm.trans hb.symm

end PiPolynomialValues.FourPeriod
