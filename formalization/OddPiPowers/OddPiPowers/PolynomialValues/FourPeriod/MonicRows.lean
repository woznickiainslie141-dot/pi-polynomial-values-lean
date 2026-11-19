module

public import OddPiPowers.PolynomialValues.FourPeriod.PrefixMinor
public import OddPiPowers.PolynomialValues.FourPeriod.RowMultiplicity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A monic change of polynomial basis in every full node prefix leaves the
actual integral determinant invariant, in any enumeration of the retained rows. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

private theorem candidate_ext {V : ℕ} {m : Fin V → ℕ} {a b : RowCandidates m}
    (hv : a.1 = b.1) (hk : a.2.val = b.2.val) : a = b := by
  obtain ⟨v,i⟩ := a
  obtain ⟨w,j⟩ := b
  dsimp only at hv hk
  subst w
  exact congrArg (Sigma.mk v) (Fin.ext hk)

private theorem det_one_of_prefix_support {R : Type*} [CommRing R] {V n : ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (T : Matrix (Fin n) (Fin n) R)
    (hd : ∀ i, T i i = 1)
    (hs : ∀ i k, T i k ≠ 0 → (e i).1 = (e k).1 ∧ (e k).2.val ≤ (e i).2.val) : T.det = 1 := by
  classical
  rw [Matrix.det_apply']
  refine (sum_eq_single 1 ?_ ?_).trans ?_
  · intro σ _ hne
    have hz : ∃ i, T (σ i) i = 0 := by
      by_contra! hall
      let grade (i : Fin n) := (e i).2.val
      have hle (i : Fin n) (_ : i ∈ univ) : grade i ≤ grade (σ i) := (hs _ _ (hall i)).2
      have he := (sum_eq_sum_iff_of_le hle).mp (Equiv.sum_comp σ grade).symm
      apply hne
      exact Equiv.ext (fun i => e.injective (candidate_ext (hs _ _ (hall i)).1 (he i (mem_univ _)).symm))
    obtain ⟨i,hi⟩ := hz
    rw [prod_eq_zero (f := fun k => T (σ k) k) (mem_univ i) hi, mul_zero]
  · simp
  · simp [hd]

private theorem sum_prefix_fiber {R : Type*} [AddCommMonoid R] {V : ℕ} (m : Fin V → ℕ)
    (v : Fin V) (f : ℕ → R) :
    (∑ a : RowCandidates m, if a.1 = v then f a.2.val else 0) = ∑ k ∈ range (m v), f k := by
  rw [Fintype.sum_sigma]
  rw [sum_eq_single v]
  · simpa only [if_pos rfl, ite_true] using Fin.sum_univ_eq_sum_range f (m v)
  · intro w _ hw
    simp [hw]
  · simp

noncomputable def rowPolynomialMatrix {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (p : Fin n → GaussianInt[X]) :
    Matrix (Fin n) (Fin n) GaussianInt[X] :=
  Matrix.of fun i j => entryWithRow (node (e i).1) (cols j).1 (cols j).2 (p i)

theorem rowPolynomialMatrix_det {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (p : Fin n → GaussianInt[X])
    (hdeg : ∀ i, (p i).natDegree ≤ (e i).2.val)
    (hmon : ∀ i, (p i).coeff (e i).2.val = 1) :
    (rowPolynomialMatrix e node cols p).det =
      rawDeterminant (fun i => (node (e i).1, (e i).2.val)) cols := by
  classical
  let T : Matrix (Fin n) (Fin n) GaussianInt[X] := Matrix.of fun i k =>
    if (e k).1 = (e i).1 then C ((p i).coeff (e k).2.val) else 0
  let A : Matrix (Fin n) (Fin n) GaussianInt[X] := Matrix.of fun k j =>
    rawEntry (node (e k).1) (cols j).1 (e k).2.val (cols j).2
  have hT : T.det = 1 := by
    apply det_one_of_prefix_support e T (fun i => by simp [T,hmon])
    intro i k hk
    by_cases hv : (e k).1 = (e i).1
    · refine ⟨hv.symm, ?_⟩
      by_contra! hl
      exact hk (by simp [T,hv,coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt hl)])
    · exact False.elim (hk (by simp [T,hv]))
  have hM : rowPolynomialMatrix e node cols p = T * A := by
    apply Matrix.ext
    intro i j
    let f (k : ℕ) := C ((p i).coeff k) * rawEntry (node (e i).1) (cols j).1 k (cols j).2
    let F (a : RowCandidates m) := if a.1 = (e i).1 then f a.2.val else 0
    calc
      _ = ∑ k ∈ range (m (e i).1), f k :=
        entryWithRow_expansion _ _ _ _ _ ((hdeg i).trans_lt (e i).2.isLt)
      _ = ∑ a : RowCandidates m, F a := (sum_prefix_fiber m (e i).1 f).symm
      _ = ∑ k : Fin n, F (e k) := (Equiv.sum_comp e F).symm
      _ = _ := by
        rw [Matrix.mul_apply]
        apply sum_congr rfl
        intro k _
        by_cases hv : (e k).1 = (e i).1 <;> simp [F, f, T, A, hv]
  rw [hM, Matrix.det_mul, hT, one_mul]
  rfl

end PiPolynomialValues.FourPeriod
