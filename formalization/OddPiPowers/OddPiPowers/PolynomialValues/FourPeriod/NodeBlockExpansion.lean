module

public import OddPiPowers.PolynomialValues.FourPeriod.PrefixMinor
public import Mathlib.LinearAlgebra.Matrix.Block

/-! A Laplace expansion by the actual node prefixes. Each nonzero
column allocation is a product of square node blocks times a unit. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

noncomputable def nodeMask {R : Type*} [CommRing R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (A : Matrix (Fin n) (Fin n) R) (b : Fin n → Fin V) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if (e i).1 = b j then A i j else 0

theorem det_by_node_allocations {R : Type*} [CommRing R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (A : Matrix (Fin n) (Fin n) R) :
    A.det = ∑ b : Fin n → Fin V, (nodeMask e A b).det := by
  classical
  let L := (Matrix.detRowAlternating (n := Fin n) (R := R)).toMultilinearMap
  let g (j : Fin n) (v : Fin V) (i : Fin n) := if (e i).1 = v then A i j else 0
  have he : A.transpose.det = L (fun j => ∑ v, g j v) := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro j i
    simp [g,Matrix.transpose_apply]
  rw [← Matrix.det_transpose A,he,L.map_sum]
  apply sum_congr rfl
  intro b _
  rw [← Matrix.det_transpose (nodeMask e A b)]
  rfl

private noncomputable def prefixFiber {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (v : Fin V) : Fin (m v) ≃ {i : Fin n // (e i).1 = v} :=
  Equiv.ofBijective (fun k => ⟨e.symm ⟨v,k⟩,by rw [e.apply_symm_apply]⟩) (by
    constructor
    · intro x y h
      have hh := e.symm.injective (congrArg Subtype.val h)
      exact eq_of_heq (Sigma.mk.inj hh).2
    · rintro ⟨i,hi⟩
      have hs (z : RowCandidates m) (hz : z.1 = v) : ∃ k : Fin (m v), (⟨v,k⟩ : RowCandidates m) = z := by
        obtain ⟨w,k⟩ := z
        change w = v at hz
        subst w
        exact ⟨k,rfl⟩
      obtain ⟨k,hk⟩ := hs (e i) hi
      exact ⟨k,Subtype.ext (e.symm_apply_eq.mpr hk)⟩)

noncomputable def allocationBlock {R : Type*} [CommRing R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (A : Matrix (Fin n) (Fin n) R) (θ : Equiv.Perm (Fin n))
    (v : Fin V) : Matrix (Fin (m v)) (Fin (m v)) R :=
  Matrix.of fun i j => A (e.symm ⟨v,i⟩) (θ.symm (e.symm ⟨v,j⟩))

theorem nonzero_node_allocation {R : Type*} [CommRing R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (A : Matrix (Fin n) (Fin n) R) (b : Fin n → Fin V)
    (hn : (nodeMask e A b).det ≠ 0) :
    ∃ θ : Equiv.Perm (Fin n), (∀ j, (e (θ j)).1 = b j) ∧
      ∃ u : Rˣ, (nodeMask e A b).det = (u : R) * ∏ v, (allocationBlock e A θ v).det := by
  classical
  let M := nodeMask e A b
  obtain ⟨θ,hθ⟩ : ∃ θ : Equiv.Perm (Fin n), ∀ j, (e (θ j)).1 = b j := by
    by_contra! hf
    apply hn
    rw [Matrix.det_apply']
    apply sum_eq_zero
    intro θ _
    obtain ⟨j,hj⟩ := hf θ
    have hz : M (θ j) j = 0 := by simp [M,nodeMask,hj]
    change _ * (∏ i, M (θ i) i) = 0
    rw [prod_eq_zero (f := fun i => M (θ i) i) (mem_univ j) hz,mul_zero]
  let N := M.submatrix id θ.symm
  have htag (j) : b (θ.symm j) = (e j).1 := by simpa only [θ.apply_symm_apply] using (hθ (θ.symm j)).symm
  have ht : N.BlockTriangular (fun i => (e i).1) := by
    intro i j h
    change (if (e i).1 = b (θ.symm j) then A i (θ.symm j) else 0) = 0
    rw [htag,if_neg h.ne']
  have hd : N.det = ∏ v, (allocationBlock e A θ v).det := by
    rw [ht.det_fintype]
    apply prod_congr rfl
    intro v _
    rw [← Matrix.det_submatrix_equiv_self (prefixFiber e v) _]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    change (if (e (e.symm ⟨v,i⟩)).1 = b (θ.symm (e.symm ⟨v,j⟩)) then _ else 0) = _
    rw [htag,e.apply_symm_apply,e.apply_symm_apply,if_pos rfl]
    rfl
  let ε : Rˣ := Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign θ.symm)
  have hperm : N.det = (ε : R)*M.det := Matrix.det_permute' _ _
  refine ⟨θ,hθ,ε⁻¹,?_⟩
  change M.det = _ * _
  rw [← hd,hperm,← mul_assoc,Units.inv_mul,one_mul]

end PiPolynomialValues.FourPeriod
