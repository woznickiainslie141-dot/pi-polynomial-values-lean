module

public import OddPiPowers.PolynomialValues.FourPeriod.PrefixRows
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Abel

/-! Greedy selection in a finite scan. The chosen indices give a basis
whenever a relation on the candidate columns has only the zero solution. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

abbrev RowCandidates {V : ℕ} (count : Fin V → ℕ) := (v : Fin V) × Fin (count v)

noncomputable def chosenCandidates {κ : Type*} {V : ℕ} (count delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) : Finset (RowCandidates count) := by
  classical
  exact Finset.univ.filter (fun c => rowKept delay row c.1 c.2.val)

theorem scanKey_pair_injective {V : ℕ} (delay : Fin V → ℕ) {v w : Fin V} {k l : ℕ}
    (he : scanKey delay v k = scanKey delay w l) : v = w ∧ k = l := by
  have hmod (u : Fin V) (i : ℕ) : scanKey delay u i % V = u.val := by
    simp [scanKey, Nat.add_mod, Nat.mod_eq_of_lt u.isLt]
  have h₁ := congrArg (· % V) he
  rw [hmod,hmod] at h₁
  have hw : v = w := Fin.ext h₁
  subst w
  have hV : V ≠ 0 := Nat.ne_of_gt ((Nat.zero_le v.val).trans_lt v.isLt)
  have hm : (delay v+k)*V = (delay v+l)*V := Nat.add_right_cancel he
  exact ⟨rfl,Nat.add_left_cancel (mul_right_cancel₀ hV hm)⟩

theorem scanKey_before_end {V : ℕ} (count : Fin V → ℕ) (H : ℕ) (hH : ∀ v, count v ≤ H)
    (v : Fin V) (k : ℕ) :
    scanKey (fun v => H-count v) v k < H*V ↔ k < count v := by
  unfold scanKey
  have hcount := hH v
  constructor
  · intro h
    by_contra hn
    have he : H ≤ H-count v+k := by omega
    have hh := Nat.mul_le_mul_right V he
    exact (not_lt_of_ge (hh.trans (Nat.le_add_right _ _))) h
  · intro h
    have he : (H-count v+k)+1 ≤ H := by omega
    calc
      _ < (H-count v+k)*V+V := Nat.add_lt_add_left v.isLt _
      _ = (H-count v+k+1)*V := by ring
      _ ≤ H*V := Nat.mul_le_mul_right _ he

private theorem independent_at_keys {ι κ : Type*} [Fintype ι] (key : ι → ℕ)
    (hi : Function.Injective key) (v : ι → κ → ℂ) (W : ℕ → Submodule ℂ (κ → ℂ))
    (out : ∀ i, v i ∉ W (key i)) (earlier : ∀ i j, key j < key i → v j ∈ W (key i)) :
    LinearIndependent ℂ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hz i
  by_contra hgi
  let s := Finset.univ.filter (fun k => g k ≠ 0)
  obtain ⟨m,hm,hmx⟩ := s.exists_max_image key ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgi⟩⟩
  have hgm := (Finset.mem_filter.mp hm).2
  let rest := ∑ j ∈ Finset.univ.erase m, g j • v j
  have hr : rest ∈ W (key m) := by
    apply Submodule.sum_mem
    intro j hj
    by_cases h : g j = 0
    · simp [h]
    · have hle := hmx j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have hlt : key j < key m := lt_of_le_of_ne hle
        (fun r => (Finset.mem_erase.mp hj).1 (hi r))
      exact (W (key m)).smul_mem _ (earlier m j hlt)
  have he : rest+g m • v m = 0 :=
    (Finset.sum_erase_add Finset.univ (fun j => g j • v j) (Finset.mem_univ m)).trans hz
  have hmem : g m • v m ∈ W (key m) := by
    have hneg : g m • v m = -rest := by
      calc
        _ = -rest+(rest+g m • v m) := by abel
        _ = _ := by rw [he,add_zero]
    rw [hneg]
    exact (W (key m)).neg_mem hr
  apply out m
  simpa only [smul_smul, inv_mul_cancel₀ hgm, one_smul] using
    (W (key m)).smul_mem ((g m)⁻¹) hmem

theorem chosenCandidates_independent {V : ℕ} {κ : Type*} (count delay : Fin V → ℕ)
    (row : Fin V → ℕ → κ → ℂ) :
    LinearIndependent ℂ (fun c : ↥(chosenCandidates count delay row) => row c.val.1 c.val.2.val) := by
  classical
  refine independent_at_keys (fun c : ↥(chosenCandidates count delay row) => scanKey delay c.val.1 c.val.2.val)
    ?_ _ (earlierRows delay row) ?_ ?_
  · intro i j he
    obtain ⟨h₁,h₂⟩ := scanKey_pair_injective delay he
    apply Subtype.ext
    obtain ⟨⟨v,iv⟩,hi⟩ := i
    obtain ⟨⟨w,iw⟩,hj⟩ := j
    dsimp only at h₁ h₂ ⊢
    subst w
    exact congrArg (Sigma.mk v) (Fin.ext h₂)
  · intro i
    exact (Finset.mem_filter.mp i.property).2
  · intro i j h
    exact Submodule.subset_span ⟨j.val.1,j.val.2.val,h,rfl⟩

theorem span_of_trivial_candidate_kernel {κ ι : Type*} [Fintype κ] [Fintype ι]
    (row : ι → κ → ℂ) (h : ∀ a : κ → ℂ, (∀ i, ∑ j, a j*row i j = 0) → a = 0) :
    Submodule.span ℂ (Set.range row) = ⊤ := by
  classical
  let A : Matrix ι κ ℂ := Matrix.of row
  have hcol : LinearIndependent ℂ A.col := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hz j
    have hg := h g (fun i => by
      have hh := congrFun hz i
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, Matrix.col,
        A, Matrix.transpose_apply, Matrix.of_apply] using hh)
    exact congrFun hg j
  have hrank := Matrix.vecMul_surjective_iff_rank_eq_card.mp hcol.vecMul_surjective
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank ℂ (Submodule.span ℂ (Set.range A.row)) = _
  rw [← A.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]

theorem chosenCandidates_span {κ : Type*} {V : ℕ} (count : Fin V → ℕ) (H : ℕ)
    (hH : ∀ v, count v ≤ H) (row : Fin V → ℕ → κ → ℂ) :
    Submodule.span ℂ (Set.range (fun c : ↥(chosenCandidates count (fun v => H-count v) row) =>
      row c.val.1 c.val.2.val)) =
      Submodule.span ℂ (Set.range (fun c : RowCandidates count => row c.1 c.2.val)) := by
  classical
  let delay := fun v => H-count v
  have he (v : Fin V) (k : ℕ) : scanKey delay v k < H*V ↔ k < count v :=
    scanKey_before_end count H hH v k
  have full : earlierRows delay row (H*V) =
      Submodule.span ℂ (Set.range (fun c : RowCandidates count => row c.1 c.2.val)) := by
    apply congrArg (Submodule.span ℂ)
    ext x
    constructor
    · rintro ⟨v,k,hk,rfl⟩
      exact ⟨⟨v,k,(he v k).mp hk⟩,rfl⟩
    · rintro ⟨⟨v,k⟩,rfl⟩
      exact ⟨v,k.val,(he v k.val).mpr k.isLt,rfl⟩
  rw [← full,keptRows_span]
  apply congrArg (Submodule.span ℂ)
  ext x
  constructor
  · rintro ⟨⟨⟨v,k⟩,hin⟩,rfl⟩
    exact ⟨v,k.val,(he v k.val).mpr k.isLt,(Finset.mem_filter.mp hin).2,rfl⟩
  · rintro ⟨v,k,hk,hkeep,rfl⟩
    let c : RowCandidates count := ⟨v,k,(he v k).mp hk⟩
    exact ⟨⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkeep⟩⟩,rfl⟩

end PiPolynomialValues.FourPeriod
