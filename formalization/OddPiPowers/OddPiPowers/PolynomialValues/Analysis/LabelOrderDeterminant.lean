module

public import OddPiPowers.PolynomialValues.FourPeriod.OriginOrder
import all OddPiPowers.PolynomialValues.FourPeriod.OriginOrder
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Finite coefficient directions indexed by a label and a Taylor power.
Repeated directions vanish by alternation. Row derivatives subtract their
actual total order from the resulting power of the local parameter. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def labelPairs {n : ℕ} (q : Fin n → ℕ) : ℕ :=
  ∑ l ∈ univ.image q, ((univ.filter (fun c => q c=l)).card).choose 2

theorem labelPairs_le {n : ℕ} (q k : Fin n → ℕ) (hi : Function.Injective (fun c => (q c,k c))) :
    labelPairs q ≤ ∑ c, k c := by
  let S (l : ℕ) := univ.filter (fun c => q c=l)
  have hinj (l) : Set.InjOn k (S l) := by
    intro i hi' j hj he
    exact hi (Prod.ext ((mem_filter.mp hi').2.trans (mem_filter.mp hj).2.symm) he)
  calc
    labelPairs q ≤ ∑ l ∈ univ.image q, ∑ i ∈ S l, k i := by
      apply sum_le_sum
      intro l _
      have h := choose_two_le_sum ((S l).image k)
      rwa [card_image_of_injOn (hinj l),sum_image (hinj l)] at h
    _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem q hi) k

theorem det_dvd_of_entry_congr {R : Type*} [CommRing R] {n : ℕ} (d : R)
    (A B : Matrix (Fin n) (Fin n) R) (he : ∀ i j, d ∣ A i j-B i j)
    (hb : d ∣ B.det) : d ∣ A.det := by
  let I : Ideal R := Ideal.span {d}
  let φ := Ideal.Quotient.mk I
  have hd (x : R) : φ x=0 ↔ d ∣ x := Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hm : φ.mapMatrix A = φ.mapMatrix B := by
    ext i j
    change φ (A i j) = φ (B i j)
    rw [← sub_eq_zero,← map_sub]
    exact (hd _).mpr (he i j)
  apply (hd _).mp
  rw [φ.map_det,hm,← φ.map_det]
  exact (hd _).mpr hb

theorem labelled_truncation_dvd {R : Type*} [CommRing R] {n K : ℕ}
    (W : R) (q σ : Fin n → ℕ) (a : Fin n → Fin K → R) (D : ℕ → Fin K → Fin n → R)
    (hD : ∀ q k i, W^(k.val-σ i) ∣ D q k i) :
    W^(labelPairs q-∑ i, σ i) ∣ (Matrix.of (fun i c => ∑ k, a c k*D (q c) k i)).det := by
  classical
  let A := Matrix.of (fun i c => ∑ k, a c k*D (q c) k i)
  let L := (Matrix.detRowAlternating (n := Fin n) (R := R)).toMultilinearMap
  have he : A.transpose.det = L (fun c => ∑ k, a c k • D (q c) k) := by
    apply congrArg Matrix.det
    ext i j
    simp [A,Pi.smul_apply]
  change _ ∣ A.det
  rw [← Matrix.det_transpose A,he,L.map_sum]
  apply dvd_sum
  intro k _
  rw [L.map_smul_univ,smul_eq_mul]
  apply dvd_mul_of_dvd_right
  let M := Matrix.of (fun c i => D (q c) (k c) i)
  change _ ∣ M.det
  by_cases hi : Function.Injective (fun c => (q c,(k c).val))
  · have hK := labelPairs_le q (fun c => (k c).val) hi
    rw [Matrix.det_apply']
    apply dvd_sum
    intro θ _
    apply dvd_mul_of_dvd_right
    have hσ : (∑ c, σ (θ.symm c)) = ∑ i, σ i := Equiv.sum_comp θ.symm σ
    have hπ : (∑ i, (k (θ i)).val) = ∑ c, (k c).val := Equiv.sum_comp θ (fun c => (k c).val)
    have hle : (∑ i, (k (θ i)).val) ≤ (∑ i, ((k (θ i)).val-σ i)) + ∑ i, σ i := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun i _ => by omega
    apply (pow_dvd_pow W (show labelPairs q-(∑ i, σ i) ≤ ∑ i, ((k (θ i)).val-σ i) by omega)).trans
    rw [← prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ (fun i _ => hD _ _ _)
  · obtain ⟨i,j,hh,hne⟩ := Function.not_injective_iff.mp hi
    have hq := congrArg Prod.fst hh
    have hk : k i=k j := Fin.ext (congrArg Prod.snd hh)
    have hz : M.det=0 := by
      apply Matrix.det_zero_of_row_eq hne
      change D (q i) (k i) = D (q j) (k j)
      change q i=q j at hq
      rw [hq,hk]
    rw [hz]
    exact dvd_zero _

end PiPolynomialValues.FourPeriod
