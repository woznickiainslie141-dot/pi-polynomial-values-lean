module

public import OddPiPowers.PolynomialValues.RootRateLimits
public import Mathlib.Order.Filter.Finite

/-! Select a constant positive degree along the escaping sequence, and
enumerate the genuine conjugates with their closest member first. -/

@[expose] public section

namespace PiPolynomialValues

open Filter Polynomial Set Finset Real
open scoped Topology

theorem fixed_degree_subsequence {d : ℕ} (p : ℕ → ℤ[X]) (H : ∀ i, PrimitiveInput d (p i)) :
    ∃ k : ℕ, k+1≤d ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, (p (φ i)).natDegree=k+1 := by
  let f (i : ℕ) : Fin (d+1) := ⟨(p i).natDegree, Nat.lt_succ_of_le (H i).2.2.2⟩
  have h : ∃ᶠ i in atTop, ∃ j∈(Set.univ : Set (Fin (d+1))), f i=j :=
    (Eventually.of_forall (fun i => ⟨f i,Set.mem_univ _,rfl⟩)).frequently
  obtain ⟨j,_,hj⟩ := (frequently_exists_finite Set.finite_univ).mp h
  obtain ⟨φ,hφ,he⟩ := extraction_of_frequently_atTop hj
  have hdeg (i : ℕ) : (p (φ i)).natDegree=j.val := congrArg Fin.val (he i)
  have hpos := (H (φ 0)).2.2.1
  have hjpos : 0<j.val := hdeg 0 ▸ hpos
  refine ⟨j.val-1,by have := j.isLt; omega,φ,hφ,fun i => ?_⟩
  rw [hdeg i]; omega

def enumList {A : Type*} (xs : List A) {k : ℕ} (h : xs.length=k) (i : Fin k) := xs.get (i.cast h.symm)

theorem ofFn_enumList {A : Type*} (xs : List A) {k : ℕ} (h : xs.length=k) :
    List.ofFn (enumList xs h)=xs := by
  subst k
  exact List.ofFn_get xs

noncomputable def indexedRoot (p : ℤ[X]) (ξ : ℂ) {k : ℕ} (hd : p.natDegree=k) :=
  enumList (orderedRoots p ξ) ((orderedRoots_length p ξ).trans hd)

theorem ofFn_indexedRoot (p : ℤ[X]) (ξ : ℂ) {k : ℕ} (hd : p.natDegree=k) :
    List.ofFn (indexedRoot p ξ hd)=orderedRoots p ξ := ofFn_enumList _ _

theorem indexed_root_mem (p : ℤ[X]) (ξ : ℂ) {k : ℕ} (hd : p.natDegree=k) (j : Fin k) :
    indexedRoot p ξ hd j∈(p.map (Int.castRingHom ℂ)).roots := by
  rw [← orderedRoots_multiset p ξ,← ofFn_indexedRoot p ξ hd]
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

theorem pi_not_integer_root (p : ℤ[X]) (hp : p≠0) (hd : p.natDegree≤3) {z : ℂ}
    (h : z∈(p.map (Int.castRingHom ℂ)).roots) : (π : ℂ)≠z := by
  rintro rfl
  have hv := (isRoot_of_mem_roots h)
  change (p.map (Int.castRingHom ℂ)).eval (π : ℂ)=0 at hv
  rw [eval_map,complex_value_at_real,Complex.ofReal_eq_zero] at hv
  exact pi_cubic_value_ne_zero p hp hd hv

theorem sum_indexed_roots (p : ℤ[X]) (ξ : ℂ) {k : ℕ} (hd : p.natDegree=k) (f : ℂ → ℝ) :
    ((p.map (Int.castRingHom ℂ)).roots.map f).sum=∑ j, f (indexedRoot p ξ hd j) := by
  rw [← orderedRoots_multiset p ξ,← ofFn_indexedRoot p ξ hd]
  simp only [Multiset.map_coe,Multiset.sum_coe,List.map_ofFn,Fin.sum_ofFn,Function.comp_apply]

theorem secondary_indexed_budget (p : ℤ[X]) (ξ : ℂ) {k : ℕ} (hd : p.natDegree=k+1) (hd3 : p.natDegree≤3)
    (hi : Irreducible (p.map (Int.castRingHom ℚ))) (hn : ∀ z∈(p.map (Int.castRingHom ℂ)).roots, ξ≠z) :
    (∑ j : Fin k, rootProximity ξ (indexedRoot p ξ hd j.succ))≤(k : ℝ)*log (measure p)+3*log (2*(1+‖ξ‖)) := by
  let z := indexedRoot p ξ hd
  have he : orderedRoots p ξ=z 0::List.ofFn (fun j => z j.succ) := (ofFn_indexedRoot p ξ hd).symm.trans List.ofFn_succ
  have H := secondary_log_sum p ξ hi hd3 (z 0) _ he (fun y hy => by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy
    exact hn _ (indexed_root_mem p ξ hd j.succ))
  simpa only [hd,Nat.add_sub_cancel,List.map_ofFn,Fin.sum_ofFn,Function.comp_apply,z] using H

theorem principal_real_of_gap (p : ℤ[X]) (ξ : ℝ) {k : ℕ} (hd : p.natDegree=k+1)
    (hn : ∀ z∈(p.map (Int.castRingHom ℂ)).roots, (ξ : ℂ)≠z)
    (hg : ∀ j : Fin k, rootProximity ξ (indexedRoot p ξ hd j.succ)<rootProximity ξ (indexedRoot p ξ hd 0)) :
    ∃ x : ℝ, indexedRoot p ξ hd 0=(x : ℂ) := by
  apply closest_root_real ξ (indexed_root_mem p ξ hd 0)
  intro y hy hdist
  have hp := positive_truncated_of_ne (hn _ hy)
  have he : rootProximity ξ (indexedRoot p ξ hd 0)≤rootProximity ξ y :=
    neg_le_neg (log_le_log hp hdist)
  rw [← orderedRoots_multiset p ξ,← ofFn_indexedRoot p ξ hd] at hy
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy
  cases j using Fin.cases with
  | zero => rfl
  | succ j => exact False.elim ((hg j).not_ge he)

end PiPolynomialValues
