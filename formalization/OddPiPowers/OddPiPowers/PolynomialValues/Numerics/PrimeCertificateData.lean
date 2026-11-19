module

public import OddPiPowers.PolynomialValues.Numerics.SlabRewards
public import OddPiPowers.PolynomialValues.Numerics.ActiveTailLevels
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticPrimeCost
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicPrimeCost
import all Mathlib.Data.List.Sort

/-! The two checked numerical ledgers, with the separation of residue
windows and level intervals and enough baseline for every lattice saving. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow Finset

structure PrimeCertificate (s : Shape) (g : List (List ℤ)) (K T : ℕ) (cuts : List ℚ)
    (slabs : List Slab) : Prop extends PrimeShapeData s g K where
  split_pos : 0 < T
  ceiling_ge : s.massUnit ≤ maxRowUnits s
  pad_four : 4 ≤ s.widths.length+1
  enough : 10*s.massUnit ≤ baseCoefficient s
  slabs_ok : slabsPass s ⟨T,1⟩ slabs = true
  gain_cap : ∀ z ∈ slabs, (z.boxes.map Box.gain).sum ≤ 10
  cut_range : ∀ q ∈ cuts, 1/(T : ℚ) ≤ q ∧ q ≤ s.largestRowQ

theorem quadratic_prime_certificate :
    PrimeCertificate quadraticShape quadraticNodeGroups 73 5 quadraticTailCuts quadraticSlabs := by
  refine ⟨quadratic_prime_shape_data,by decide,by decide +kernel,by decide,by decide +kernel,
    quadraticSlabs_checked.valid,?_,?_⟩
  · decide +kernel
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp quadraticTail_cuts_inside.1 q hq)

theorem cubic_prime_certificate :
    PrimeCertificate cubicShape cubicNodeGroups 229 8 cubicTailCuts cubicSlabs := by
  refine ⟨cubic_prime_shape_data,by decide,by decide +kernel,by decide,by decide +kernel,
    cubicSlabs_checked.valid,?_,?_⟩
  · decide +kernel
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp cubicTail_cuts_inside.1 q hq)

variable {s : Shape} {g : List (List ℤ)} {K T : ℕ} {cuts : List ℚ} {slabs : List Slab}

theorem PrimeCertificate.largest_pos (C : PrimeCertificate s g K T cuts slabs) : 0 < s.largestRowQ :=
  div_pos (by exact_mod_cast C.mass_pos.trans_le C.ceiling_ge) (by exact_mod_cast C.mass_pos)

theorem PrimeCertificate.cut_pos (C : PrimeCertificate s g K T cuts slabs) {q : ℚ} (hq : q ∈ cuts) :
    0 < q ∧ q ≤ s.largestRowQ :=
  ⟨(div_pos one_pos (by exact_mod_cast C.split_pos)).trans_le (C.cut_range q hq).1,(C.cut_range q hq).2⟩

theorem PrimeCertificate.cut_prime_bounds (C : PrimeCertificate s g K T cuts slabs) {u t p : ℕ}
    (hu : u < cuts.length) (hp : p ∈ primeSlice (cutAt cuts u) s.largestRowQ (s.massUnit*t)) :
    s.massUnit*t < T*p ∧ p ∈ Nat.primesLE (primeCeiling s t) := by
  let N := s.massUnit*t
  have h := (mem_primeSlice (cutAt cuts u) s.largestRowQ (by exact_mod_cast C.largest_pos.le) N p).mp hp
  have hT : (0 : ℝ) < T := by exact_mod_cast C.split_pos
  have hlo : 1/(T : ℝ) ≤ (cutAt cuts u : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (C.cut_range _ (cutAt_mem hu)).1
  have h₁ := (mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg N)).trans_lt h.2.1
  rw [show 1/(T : ℝ)*N = N/T by ring] at h₁
  have he := primeCeiling_eq s t C.mass_pos
  change (primeCeiling s t : ℝ) = (s.largestRowQ : ℝ)*N + _ at he
  have hpad : (0 : ℝ) ≤ ((s.widths.length+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h₂ : (p : ℝ) ≤ primeCeiling s t := by linarith only [h.2.2,he,hpad]
  exact ⟨by exact_mod_cast (div_lt_iff₀ hT).mp h₁ |>.trans_eq (mul_comm (p : ℝ) T),
    Nat.mem_primesLE.mpr ⟨by exact_mod_cast h₂,h.1⟩⟩

theorem PrimeCertificate.residue_beyond_split (C : PrimeCertificate s g K T cuts slabs) {z : Slab} (hz : z ∈ slabs)
    {t p : ℕ} (he : z.Eligible s K t p) : T*p < s.massUnit*t := by
  have hc := checked_in_slabs slabs s ⟨T,1⟩ Nat.zero_lt_one C.slabs_ok z hz
  have hT : (T : ℝ) ≤ z.left.value := by simpa [Abscissa.value] using hc.starts
  obtain ⟨hp,_,δ,hd,hlo,_⟩ := he
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h : (T : ℝ) < ((s.massUnit*t : ℕ) : ℝ)/p := by linarith only [hT,hd,hlo]
  exact_mod_cast (lt_div_iff₀ hp').mp h

end PiPolynomialValues.FourPeriod
