module

public import OddPiPowers.PolynomialValues.FourPeriod.PrimeLevelCounts
public import OddPiPowers.PolynomialValues.FourPeriod.ActualDegree

/-! The complete consecutive band and each actual row prefix give
positive-part counts with no asymptotic approximation. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

theorem grade_div_iff (a b p h : ℕ) (hp : 0 < p) :
    h ≤ a+b/p ↔ (h-a)*p ≤ b := by
  rw [← Nat.le_div_iff_mul_le hp]
  generalize b/p = q
  omega

private theorem column_band_tail (U j p h : ℕ) (hp : 0 < p) :
    (∑ x : ↥(Icc (-(U : ℤ)) (U : ℤ)),
      if h ≤ j+(x.val+U).toNat/4/p then 1 else 0) = 2*U+1-4*((h-j)*p) := by
  let I := Icc (-(U : ℤ)) (U : ℤ)
  let q := (h-j)*p
  change (∑ x : ↥I, if h ≤ j+(x.val+U).toNat/4/p then 1 else 0) = 2*U+1-4*q
  rw [I.sum_coe_sort (fun x : ℤ => if h ≤ j+(x+U).toNat/4/p then (1 : ℕ) else 0),sum_boole,Nat.cast_id]
  have he : I.filter (fun x : ℤ => h ≤ j+(x+(U : ℤ)).toNat/4/p) = Icc ((4*q : ℕ)-(U : ℤ)) (U : ℤ) := by
    ext x
    simp only [I,mem_filter,mem_Icc,grade_div_iff j _ p h hp,Nat.le_div_iff_mul_le (by decide : 0 < 4)]
    change ((-(U : ℤ) ≤ x ∧ x ≤ U) ∧ q*4 ≤ (x+U).toNat) ↔ _
    push_cast
    omega
  rw [he,Int.card_Icc]
  push_cast
  omega

theorem columnLevelCount_eq {n J : ℕ} {U : Fin J → ℕ} (d : Fin n ≃ Column U) (p h : ℕ) (hp : 0 < p) :
    columnLevelCount d p h = ∑ j, (2*U j+1-4*((h-j.val)*p)) := by
  let f (c : Column U) : ℕ := if h ≤ c.1.val+columnOrder c/p then 1 else 0
  have he : columnLevelCount d p h = ∑ i, f (d i) := by simp [columnLevelCount,f]
  rw [he,Equiv.sum_comp d f,Fintype.sum_sigma]
  exact sum_congr rfl (fun j _ => column_band_tail (U j) j.val p h hp)

private theorem single_row_tail (m q p h : ℕ) (hp : 0 < p) :
    (∑ k : Fin m, if h ≤ k.val/p+q then 1 else 0) = m-(h-q)*p := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if h ≤ k/p+q then (1 : ℕ) else 0) m,
    sum_boole,Nat.cast_id]
  have he : (range m).filter (fun k => h ≤ k/p+q) = Ico ((h-q)*p) m := by
    ext k
    rw [mem_filter,mem_range,mem_Ico,Nat.add_comm (k/p) q,grade_div_iff q k p h hp]
    exact and_comm
  rw [he,Nat.card_Ico]

theorem actual_row_tail {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (rank : Fin V → ℕ)
    (hi : Function.Injective (fun v => (node v % 4,rank v))) (p h : ℕ) (hp : 0 < p) :
    rowLevelCount (fun i => (node (e i).1,(e i).2.val)) p h ≤
      ∑ v, (m v - (h-rank v)*p) := by
  let rows (i : Fin n) := (node (e i).1,(e i).2.val)
  have hinj : Function.Injective (fun i => (rowTag (rows i),rank (e i).1)) := by
    intro i j hij
    have hv : (e i).1 = (e j).1 :=
      hi (Prod.ext (congrArg (fun d : (ℤ × ℕ) × ℕ => d.1.1) hij)
        (congrArg (fun d : (ℤ × ℕ) × ℕ => d.2) hij))
    have hk : (e i).2.val = (e j).2.val := congrArg (fun d => d.1.2) hij
    apply e.injective
    generalize ei : e i = vi at hv hk ⊢
    generalize ej : e j = vj at hv hk ⊢
    obtain ⟨u,x⟩ := vi
    obtain ⟨v,z⟩ := vj
    change u = v at hv
    subst v
    exact congrArg (Sigma.mk u) (Fin.ext hk)
  apply (rowLevelCount_le_rank rows _ hinj p h).trans_eq
  let f (z : RowCandidates m) : ℕ := if h ≤ z.2.val/p+rank z.1 then 1 else 0
  change ∑ i, f (e i) = _
  rw [Equiv.sum_comp e f,Fintype.sum_sigma]
  exact sum_congr rfl (fun v _ => single_row_tail (m v) (rank v) p h hp)

def scannedRank (g : List (List ℤ)) (v : Fin g.flatten.length) : ℕ :=
  (g.flatMap (fun grp => List.range grp.length))[v.val]?.getD 0

theorem quadratic_ranks_injective : Function.Injective (fun v =>
    (scannedNode quadraticNodeGroups v % 4,scannedRank quadraticNodeGroups v)) := by decide +kernel

theorem cubic_ranks_injective : Function.Injective (fun v =>
    (scannedNode cubicNodeGroups v % 4,scannedRank cubicNodeGroups v)) := by decide +kernel

end PiPolynomialValues.FourPeriod
