module

public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxActual
public import OddPiPowers.PolynomialValues.FourPeriod.ResiduePairs
public import OddPiPowers.PolynomialValues.FourPeriod.Columns
import Mathlib.Tactic.Ring

/-! Count the actual labeled columns in every prime residue exactly,
including zero, endpoints of bands and repeated frequencies in different layers. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset

theorem residueTag_fin {p : ℕ} (hp : 0 < p) (r : Fin p) : residueTag hp (r.val : ℤ) = r := by
  apply Fin.ext
  change (((r.val : ℤ) % (p : ℤ)).toNat) = r.val
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt)]
  simp

theorem band_lifts_card (w N p U : ℕ) (hp : 0 < p) (hU : w*N = 10000*U) (r : Fin p) :
    (lifts w ((N : ℝ)/p) ((r.val : ℝ)/p)).card =
      ((Icc (-(U : ℤ)) (U : ℤ)).filter (fun x => residueTag hp x = r)).card := by
  have hscale : (w : ℤ)*N = 10000*(U : ℤ) := by exact_mod_cast hU
  have hr : ((r.val : ℤ) : ℝ) = (r.val : ℝ) := by simp
  have hmem (k : ℤ) : k ∈ lifts w ((N : ℝ)/p) ((r.val : ℝ)/p) ↔
      k*(p : ℤ)+r.val ∈ Icc (-(U : ℤ)) (U : ℤ) := by
    rw [← hr,actual_band_membership w N p hp,mem_Icc,hscale]
    have he : |k*(p : ℤ)+(r.val : ℤ)| * 10000 ≤ 10000*(U : ℤ) ↔
        |k*(p : ℤ)+(r.val : ℤ)| ≤ (U : ℤ) := by omega
    rw [he,abs_le]
  apply card_bij (fun k _ => k*(p : ℤ)+r.val)
  · intro k hk
    refine mem_filter.mpr ⟨(hmem k).mp hk,?_⟩
    apply Eq.trans _ (residueTag_fin hp r)
    rw [residueTag_eq_iff,Int.modEq_iff_dvd]
    exact ⟨-k,by ring⟩
  · intro k _ j _ he
    exact mul_right_cancel₀ (Int.natCast_ne_zero.mpr hp.ne') (add_right_cancel he)
  · intro x hx
    obtain ⟨hb,ht⟩ := mem_filter.mp hx
    have hz := (residueTag_eq_iff hp (r.val : ℤ) x).mp ((residueTag_fin hp r).trans ht.symm)
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hz
    have he : k*(p : ℤ)+r.val = x := by rw [mul_comm,← hk]; ring
    exact ⟨k,(hmem k).mpr (he ▸ hb),he⟩

theorem actual_column_inventory (s : Shape) (t : ℕ) {n p : ℕ}
    (d : Fin n ≃ Column (s.band t)) (hp : 0 < p) (r : Fin p) :
    (residueMultiplicity hp (fun i => (columnLabel (d i)).1) r : ℤ) =
      (s.widths.map (fun w => bandCount w (((s.massUnit*t : ℕ) : ℝ)/p) ((r.val : ℝ)/p))).sum := by
  let N := s.massUnit*t
  let f (c : Column (s.band t)) : ℕ := if residueTag hp (columnLabel c).1 = r then 1 else 0
  let b (w : ℕ) := bandCount w ((N : ℝ)/p) ((r.val : ℝ)/p)
  have hen : residueMultiplicity hp (fun i => (columnLabel (d i)).1) r = ∑ c, f c := by
    rw [← Equiv.sum_comp d f]
    simp only [f,sum_boole,Nat.cast_id,residueMultiplicity]
  have ht (j : Fin s.widths.length) : ((∑ x, f ⟨j,x⟩ : ℕ) : ℤ) = b (s.widths.get j) := by
    have hh : s.widths.get j*N = 10000*(s.band t j) := by unfold N Shape.massUnit Shape.band; ring
    rw [show b (s.widths.get j) = _ from bandCount_eq_card _ (show 0 ≤ (N : ℝ)/p by positivity) _,
      band_lifts_card _ _ _ _ hp hh r, Nat.cast_inj]
    let I := Icc (-(s.band t j : ℤ)) (s.band t j : ℤ)
    change (∑ x : ↥I, if residueTag hp x.val = r then 1 else 0) =
      (I.filter (fun x => residueTag hp x = r)).card
    rw [I.sum_coe_sort (fun x : ℤ => if residueTag hp x = r then (1 : ℕ) else 0)]
    simp only [sum_boole,Nat.cast_id]
  rw [hen,Fintype.sum_sigma,Nat.cast_sum,Finset.sum_congr rfl (fun j _ => ht j)]
  change (∑ j, b (s.widths.get j)) = (s.widths.map b).sum
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.map_ofFn.symm.trans (congrArg (List.map b) (List.ofFn_get s.widths)))

theorem bandCount_reflect (w : ℕ) (t τ : ℝ) : bandCount w t (1-τ) = bandCount w t τ := by
  let a := (w : ℝ)/10000*t
  change 1+⌊a-(1-τ)⌋+⌊a+(1-τ)⌋ = 1+⌊a-τ⌋+⌊a+τ⌋
  rw [show a-(1-τ) = (a+τ)-1 by ring,show a+(1-τ) = (a-τ)+1 by ring,
    Int.floor_sub_one,Int.floor_add_one]
  omega

end PiPolynomialValues.PrimeWindow
