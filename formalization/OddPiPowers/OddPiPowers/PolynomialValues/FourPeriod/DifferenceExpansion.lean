module

public import OddPiPowers.PolynomialValues.FourPeriod.LargePrimeEntry
public import OddPiPowers.PolynomialValues.FourPeriod.ColumnDifferenceMatrix
public import OddPiPowers.PolynomialValues.FourPeriod.OriginOrder

/-! Expand the actual determinant on each row into powers of its node.
A contributing term uses different powers at every fixed residue and
row order, while retaining the column forward differences. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

noncomputable def columnKernel {J : ℕ} {U : Fin J → ℕ} (a : ℤ) (tag : ℤ × ℕ)
    (h : ℕ) (c : Column U) : GaussianInt :=
  differencedKernel a tag.1 (columnStart c) c.1.val tag.2 (columnOrder c) h

def columnPrimeExponent {J : ℕ} {U : Fin J → ℕ} (p σ h : ℕ) (c : Column U) : ℕ :=
  σ/p - min (c.1.val-h) (σ/p-columnOrder c/p)

private theorem column_expansion {J : ℕ} {U : Fin J → ℕ} (a v : ℤ) (σ : ℕ) (c : Column U) :
    ((fwdDiff (4 : ℤ))^[columnOrder c]) (fun u => entryWithRow v u c.1.val (gaussianNewton 4 a σ))
      (columnStart c) =
      ∑ h : Fin (J+1), (C ((v : GaussianInt)^h.val)*X^h.val) *
        C (columnKernel a (rowTag (v,σ)) h.val c) := by
  let P := ((fwdDiff (4 : ℤ))^[columnOrder c]) (fun u => entryWithRow v u c.1.val (gaussianNewton 4 a σ))
    (columnStart c)
  have hc (h : ℕ) : P.coeff h = (v : GaussianInt)^h * columnKernel a (rowTag (v,σ)) h c :=
    differenced_entry_coefficient _ _ _ _ _ _ _
  have hd : P.natDegree ≤ c.1.val := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro h hh
    rw [hc]
    have hz : columnKernel a (rowTag (v,σ)) h c = 0 := by
      by_contra hn
      exact hh.not_ge (differencedKernel_support hn).2
    rw [hz,mul_zero]
  let term (h : ℕ) := C (P.coeff h)*X^h
  calc
    P = ∑ h ∈ range (J+1), term h := P.as_sum_range_C_mul_X_pow' (by omega)
    _ = ∑ h : Fin (J+1), term h.val := (Fin.sum_univ_eq_sum_range term _).symm
    _ = _ := by
      apply sum_congr rfl
      intro h _
      simp only [term,hc,map_mul]
      ring

theorem raw_dvd_of_difference_matchings {V J n : ℕ} {U : Fin J → ℕ} {m : Fin V → ℕ}
    (e : Fin n ≃ RowCandidates m) (node : Fin V → ℤ) (d : Fin n ≃ Column U)
    (a : ℤ) (p g : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : ∀ i, (e i).2.val < p^2)
    (hcost : ∀ h : Fin n → ℕ, Function.Injective (fun i => (rowTag (node (e i).1,(e i).2.val),h i)) →
      ∀ θ : Equiv.Perm (Fin n),
        (∀ j, columnKernel a (rowTag (node (e (θ j)).1,(e (θ j)).2.val)) (h (θ j)) (d j) ≠ 0) →
        g ≤ ∑ j, columnPrimeExponent p (e (θ j)).2.val (h (θ j)) (d j)) :
    C ((p^g : ℕ) : GaussianInt) ∣
      rawDeterminant (fun i => (node (e i).1,(e i).2.val)) (fun j => columnLabel (d j)) := by
  classical
  let row (i : Fin n) := (node (e i).1,(e i).2.val)
  let col (j : Fin n) := columnLabel (d j)
  let f (i : Fin n) := gaussianNewton 4 a (e i).2.val
  let F (i : Fin n) (b : Fin J) (t : ℤ) := entryWithRow (node (e i).1) t b.val (f i)
  let D := Matrix.of fun i j => ((fwdDiff (4 : ℤ))^[columnOrder (d j)]) (F i (d j).1) (columnStart (d j))
  have hD : D.det = rawDeterminant row col := by
    have hr (i) : (f i).natDegree = (e i).2.val := gaussianNewton_degree _ _ _
    exact (column_difference_det d F).trans (rowPolynomialMatrix_det e node col f
      (fun i => (hr i).le) (fun i => by rw [← hr i,coeff_natDegree]; exact gaussianNewton_monic _ _ _))
  let scal (i : Fin n) (h : Fin (J+1)) : GaussianInt[X] := C ((node (e i).1 : GaussianInt)^h.val) * X^h.val
  let line (k : ℤ × ℕ) (h : Fin (J+1)) (j : Fin n) : GaussianInt[X] := C (columnKernel a k h.val (d j))
  let L := (Matrix.detRowAlternating (n := Fin n) (R := GaussianInt[X])).toMultilinearMap
  have he : D.det = L (fun i => ∑ h, scal i h • line (rowTag (row i)) h) := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    simpa only [D,Matrix.of_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,F,f,scal,line,row] using
      column_expansion a (node (e i).1) (e i).2.val (d j)
  change C ((p^g : ℕ) : GaussianInt) ∣ rawDeterminant row col
  rw [← hD,he,L.map_sum]
  apply Finset.dvd_sum
  intro h _
  rw [L.map_smul_univ,smul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hi : Function.Injective (fun i => (rowTag (row i),(h i).val))
  · change _ ∣ (Matrix.of fun i j => C (columnKernel a (rowTag (row i)) (h i).val (d j))).det
    rw [Matrix.det_apply']
    apply Finset.dvd_sum
    intro θ _
    apply dvd_mul_of_dvd_right
    by_cases hn : ∀ j, columnKernel a (rowTag (row (θ j))) (h (θ j)).val (d j) ≠ 0
    · have hle := hcost (fun i => (h i).val) hi θ hn
      rw [Nat.cast_pow,map_pow]
      apply (pow_dvd_pow (C (p : GaussianInt)) hle).trans
      rw [← prod_pow_eq_pow_sum]
      apply prod_dvd_prod_of_dvd
      intro j _
      have ht := differencedKernel_prime_power p hp hp2 a (rowTag (row (θ j))).1 (columnStart (d j))
        (d j).1.val (e (θ j)).2.val (columnOrder (d j)) (h (θ j)).val (hs (θ j))
      simpa only [columnPrimeExponent,columnKernel,rowTag,row,← map_pow,Matrix.of_apply] using
        map_dvd (C : GaussianInt →+* GaussianInt[X]) ht
    · push_neg at hn
      obtain ⟨j,hj⟩ := hn
      have hz : C (columnKernel a (rowTag (row (θ j))) (h (θ j)).val (d j)) = (0 : GaussianInt[X]) := by rw [hj,map_zero]
      simp only [Matrix.of_apply]
      rw [prod_eq_zero (f := fun j => C (columnKernel a (rowTag (row (θ j))) (h (θ j)).val (d j)))
        (mem_univ j) hz]
      exact dvd_zero _
  · obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp hi
    have ht : rowTag (row i) = rowTag (row j) := congrArg Prod.fst he
    have hh : h i = h j := Fin.ext (congrArg Prod.snd he)
    have hz : L (fun i => line (rowTag (row i)) (h i)) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      rw [ht,hh]
    rw [hz]
    exact dvd_zero _

end PiPolynomialValues.FourPeriod
