module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxLattice
public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxSum

/-! A strict first-half residue strip contains two distinct residue labels
for each integer lattice point. Folding also covers the unpaired classes. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open Finset

def foldedIndex {p : ℕ} (r : Fin p) : ℕ := min r.val (p-r.val)

def signedIndex {p : ℕ} (hp : 0 < p) (z : ℤ × Bool) : Fin p :=
  ⟨(if z.2 then p-z.1.toNat else z.1.toNat)%p,Nat.mod_lt _ hp⟩

noncomputable def foldedHits (b : Box) (N p : ℕ) : Finset (Fin p) := univ.filter fun r =>
  b.bottom.value ((N : ℝ)/p) < (foldedIndex r : ℝ)/p ∧ (foldedIndex r : ℝ)/p < b.top.value ((N : ℝ)/p)

theorem folded_lattice_card (b : Box) (N p : ℕ) (hp : 0 < p)
    (hlo : 0 ≤ b.bottom.value ((N : ℝ)/p)) (hhi : b.top.value ((N : ℝ)/p) ≤ 1/2) :
    2*(residuePoints b N p).card ≤ (foldedHits b N p).card := by
  classical
  let S := residuePoints b N p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have bounds (j : ℤ) (hj : j ∈ S) : 0 < j ∧ 2*j < (p : ℤ) := by
    have h := (mem_residuePoints b N p hp j).mp hj
    have h₀ := (lt_div_iff₀ hp').mp (hlo.trans_lt h.1)
    have h₁ := (div_lt_iff₀ hp').mp (h.2.trans_le hhi)
    constructor
    · exact_mod_cast (by linarith : (0 : ℝ) < j)
    · exact_mod_cast (by linarith : 2*(j : ℝ) < p)
  have hv (j : ℤ) (hj : j ∈ S) (c : Bool) : (signedIndex hp (j,c)).val =
      (if c then p-j.toNat else j.toNat) := by
    have h := bounds j hj
    apply Nat.mod_eq_of_lt
    cases c <;> simp <;> omega
  have hf (j : ℤ) (hj : j ∈ S) (c : Bool) : foldedIndex (signedIndex hp (j,c)) = j.toNat := by
    have h := bounds j hj
    rw [foldedIndex,hv j hj c]
    cases c <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have hc : (S ×ˢ (univ : Finset Bool)).card ≤ (foldedHits b N p).card := by
    apply card_le_card_of_injOn (signedIndex hp)
    · rintro ⟨j,c⟩ hz
      have hj : j ∈ S := (mem_product.mp hz).1
      have h := (mem_residuePoints b N p hp j).mp hj
      have hj' : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg (bounds j hj).1.le
      exact mem_filter.mpr ⟨mem_univ _,by simpa only [hf j hj c,hj'] using h⟩
    · rintro ⟨j,c⟩ hz ⟨k,d⟩ hw he
      have hj : j ∈ S := (mem_product.mp hz).1
      have hk : k ∈ S := (mem_product.mp hw).1
      have h₁ := bounds j hj
      have h₂ := bounds k hk
      have h₃ := congrArg foldedIndex he
      rw [hf j hj c,hf k hk d] at h₃
      have ej : j = k := by omega
      subst k
      have h₄ := congrArg Fin.val he
      rw [hv j hj c,hv j hj d] at h₄
      cases c <;> cases d
      · rfl
      · simp only [Bool.false_eq_true,if_false,if_true] at h₄
        omega
      · simp only [Bool.false_eq_true,if_false,if_true] at h₄
        omega
      · rfl
  simpa only [card_product,card_univ,Fintype.card_bool,mul_comm _ 2,S] using hc

noncomputable def latticeSaving (bs : List Box) (N p : ℕ) : ℕ :=
  (bs.map (fun b => 2*b.gain*(residuePoints b N p).card)).sum

theorem sum_folded_gains (bs : List Box) (N p : ℕ) (hp : 0 < p) (prev : Boundary)
    (hprev : 0 ≤ prev.value ((N : ℝ)/p)) (ho : stripOrder ((N : ℝ)/p) prev bs) :
    2*(latticeSaving bs N p : ℤ) ≤
      ∑ r : Fin p, stripGains ((N : ℝ)/p) ((foldedIndex r : ℝ)/p) bs := by
  classical
  induction bs generalizing prev with
  | nil => simp [latticeSaving,stripGains]
  | cons b bs ih =>
    obtain ⟨hb,ht,hhalf,hr⟩ := ho
    have hh := ih b.top ((hprev.trans hb).trans ht) hr
    have hc := folded_lattice_card b N p hp (hprev.trans hb) hhalf
    simp only [stripGains,sum_add_distrib]
    have he : (∑ r : Fin p, if b.bottom.value ((N : ℝ)/p) < (foldedIndex r : ℝ)/p ∧
        (foldedIndex r : ℝ)/p < b.top.value ((N : ℝ)/p) then 2*(b.gain : ℤ) else 0) =
        ((foldedHits b N p).card : ℤ)*(2*b.gain) := by
      rw [← sum_filter]
      simp [foldedHits,nsmul_eq_mul]
    rw [he]
    change 2*((2*b.gain*(residuePoints b N p).card+latticeSaving bs N p : ℕ) : ℤ) ≤ _
    push_cast
    have hc' : 2*((residuePoints b N p).card : ℤ) ≤ (foldedHits b N p).card := by exact_mod_cast hc
    nlinarith only [hh,mul_le_mul_of_nonneg_right hc' (show (0 : ℤ) ≤ 2*b.gain by positivity)]

end PiPolynomialValues.PrimeWindow
