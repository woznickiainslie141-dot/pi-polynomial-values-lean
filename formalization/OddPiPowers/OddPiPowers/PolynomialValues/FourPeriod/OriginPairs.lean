module

public import OddPiPowers.PolynomialValues.FourPeriod.PrefixMinor
public import OddPiPowers.PolynomialValues.FourPeriod.OriginOrder
public import Mathlib.Data.Finset.Prod

/-! For complete row prefixes, each pair of congruent nodes contributes
once for each order occurring at both nodes. This formula needs no ordering
of nodes with tied target sizes. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

def nodePairOrder {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ) : ℕ :=
  ∑ p ∈ (univ : Finset (Fin V)) ×ˢ univ,
    if p.1 < p.2 ∧ node p.1 % 4 = node p.2 % 4 then min (m p.1) (m p.2) else 0

def nodesAt {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ) (k : ℤ × ℕ) : Finset (Fin V) :=
  univ.filter (fun v => node v % 4 = k.1 ∧ k.2 < m v)

private theorem fiber_nodesAt {V n : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ)
    (e : Fin n ≃ RowCandidates m) (k : ℤ × ℕ) :
    (univ.filter (fun i => rowTag (node (e i).1, (e i).2.val) = k)).card =
      (nodesAt node m k).card := by
  apply Finset.card_bij (fun i _ => (e i).1)
  · intro i hi
    have he := (mem_filter.mp hi).2
    have hσ : (e i).2.val = k.2 := congrArg Prod.snd he
    exact mem_filter.mpr ⟨mem_univ _, congrArg Prod.fst he, hσ ▸ (e i).2.isLt⟩
  · intro i hi j hj hv
    have he : (e i).2.val = (e j).2.val :=
      (congrArg Prod.snd (mem_filter.mp hi).2).trans (congrArg Prod.snd (mem_filter.mp hj).2).symm
    apply e.injective
    generalize h₁ : e i = x at hv he ⊢
    generalize h₂ : e j = y at hv he ⊢
    obtain ⟨u,a⟩ := x
    obtain ⟨v,b⟩ := y
    change u = v at hv
    subst v
    exact congrArg (Sigma.mk u) (Fin.ext he)
  · intro v hv
    obtain ⟨hr,hm⟩ := (mem_filter.mp hv).2
    let p : RowCandidates m := ⟨v,k.2,hm⟩
    refine ⟨e.symm p, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [e.apply_symm_apply]
      exact Prod.ext hr rfl
    · rw [e.apply_symm_apply]

private def shared {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ)
    (k : ℤ × ℕ) (p : Fin V × Fin V) : Prop :=
  p.1 < p.2 ∧ node p.1 % 4 = k.1 ∧ node p.2 % 4 = k.1 ∧ k.2 < m p.1 ∧ k.2 < m p.2

private instance {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ) (k : ℤ × ℕ) :
    DecidablePred (shared node m k) := fun p => by unfold shared; infer_instance

private theorem choose_nodesAt {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ) (k : ℤ × ℕ) :
    (nodesAt node m k).card.choose 2 =
      ∑ p ∈ (univ : Finset (Fin V)) ×ˢ univ, if shared node m k p then 1 else 0 := by
  classical
  let F := nodesAt node m k
  have hset : ((univ : Finset (Fin V)) ×ˢ univ).filter (shared node m k) =
      (F ×ˢ F).filter (fun p => p.1 < p.2) := by
    ext p
    simp only [F, nodesAt, shared, mem_filter, mem_product, mem_univ, true_and]
    tauto
  rw [Finset.sum_boole, hset, Finset.card_product_filter_lt]
  rfl

private theorem shared_levels {V : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ)
    (H : ℕ) (hH : ∀ v, m v ≤ H) (p : Fin V × Fin V) :
    (∑ k ∈ (univ.image (fun v => node v % 4)) ×ˢ range H,
      if shared node m k p then 1 else 0) =
    (if p.1 < p.2 ∧ node p.1 % 4 = node p.2 % 4 then min (m p.1) (m p.2) else 0 : ℕ) := by
  classical
  let R := univ.image (fun v => node v % 4)
  have hr : node p.1 % 4 ∈ R := mem_image_of_mem _ (mem_univ _)
  by_cases h : p.1 < p.2 ∧ node p.1 % 4 = node p.2 % 4
  · rw [if_pos h, Finset.sum_boole]
    have hs : (R ×ˢ range H).filter (fun k => shared node m k p) =
        {node p.1 % 4} ×ˢ range (min (m p.1) (m p.2)) := by
      apply Finset.ext
      intro k
      constructor
      · intro hk
        obtain ⟨_,hr₁,_,ha,hb⟩ := (mem_filter.mp hk).2
        exact mem_product.mpr ⟨mem_singleton.mpr hr₁.symm, mem_range.mpr (lt_min ha hb)⟩
      · intro hk
        obtain ⟨hres,hlev⟩ := mem_product.mp hk
        have he := mem_singleton.mp hres
        obtain ⟨ha,hb⟩ := lt_min_iff.mp (mem_range.mp hlev)
        refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, mem_range.mpr (ha.trans_le (hH _))⟩,
          h.1,he.symm,h.2.symm.trans he.symm,ha,hb⟩
        exact he ▸ hr
    rw [hs]
    simp
  · rw [if_neg h]
    apply sum_eq_zero
    intro k _
    exact if_neg (fun he => h ⟨he.1, he.2.1.trans he.2.2.1.symm⟩)

theorem originOrder_prefix_eq {V n : ℕ} (node : Fin V → ℤ) (m : Fin V → ℕ)
    (e : Fin n ≃ RowCandidates m) :
    originOrder (fun i => (node (e i).1, (e i).2.val)) = nodePairOrder node m := by
  classical
  let tag (i : Fin n) := rowTag (node (e i).1, (e i).2.val)
  let H := ∑ v, m v
  let K := (univ.image (fun v => node v % 4)) ×ˢ range H
  have hH (v) : m v ≤ H := single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ v)
  have hk : univ.image tag ⊆ K := by
    rintro k hk
    obtain ⟨i,_,rfl⟩ := mem_image.mp hk
    exact mem_product.mpr ⟨mem_image_of_mem _ (mem_univ (e i).1),
      mem_range.mpr ((e i).2.isLt.trans_le (hH _))⟩
  change (∑ k ∈ univ.image tag, ((univ.filter (fun i => tag i = k)).card).choose 2) = _
  calc
    _ = ∑ k ∈ K, ((univ.filter (fun i => tag i = k)).card).choose 2 := by
      apply sum_subset hk
      intro k _ hn
      have hz : univ.filter (fun i => tag i = k) = ∅ := filter_eq_empty_iff.mpr
        (fun i hi he => hn (mem_image.mpr ⟨i,hi,he⟩))
      simp [hz]
    _ = ∑ k ∈ K, ∑ p ∈ (univ : Finset (Fin V)) ×ˢ univ, if shared node m k p then 1 else 0 := by
      apply sum_congr rfl
      intro k _
      rw [show (univ.filter (fun i => tag i = k)).card = (nodesAt node m k).card from fiber_nodesAt node m e k]
      exact choose_nodesAt node m k
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl (fun p _ => shared_levels node m H hH p)

end PiPolynomialValues.FourPeriod
