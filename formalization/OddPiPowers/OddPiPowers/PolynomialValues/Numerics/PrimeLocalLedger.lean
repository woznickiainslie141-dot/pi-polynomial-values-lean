module

public import OddPiPowers.PolynomialValues.Numerics.PrimeCertificateData

/-! One inequality at every prime for the four-period denominator. All
three size ranges use the same matrix and the same integer polynomial. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open PrimeWindow Finset Filter

def layerTotal (s : Shape) (t : ℕ) := scaledLayer (shapeBandUnits s)*t+layerConstant s.widths.length

theorem SelectedPolynomial.layer_sum {s : Shape} {g : List (List ℤ)} {t a b : ℕ} {y : ℂ}
    (w : SelectedPolynomial s g t y a b) : (∑ j, (w.cols j).2) = layerTotal s t :=
  (Equiv.sum_comp w.colIndex (fun c => (columnLabel c).2)).trans (column_layer_scaled (shapeBandUnits s) t)

variable {s : Shape} {g : List (List ℤ)} {K T : ℕ} {cuts : List ℚ} {slabs : List Slab}

theorem PrimeCertificate.eligible_cost (C : PrimeCertificate s g K T cuts slabs) {t a b p : ℕ} {y : ℂ}
    (w : SelectedPolynomial s g t y a b) (hp : p.Prime) {z : Slab} (hz : z ∈ slabs) (he : z.Eligible s K t p) :
    w.denominator.factorization p + latticeSaving z.boxes (s.massUnit*t) p ≤ primeBase s g K t := by
  let N := s.massUnit*t
  have hs := C.residue_beyond_split hz he
  have hpn : p ≤ N := ((show p ≤ T*p by
    simpa only [one_mul] using Nat.mul_le_mul_right p (show 1 ≤ T from C.split_pos))).trans hs.le
  have hc := checked_in_slabs slabs s ⟨T,1⟩ Nat.zero_lt_one C.slabs_ok z hz
  obtain ⟨_,hsq,δ,hd,hl,hu,hw⟩ := he
  have h₁ : z.left.value ≤ (N : ℝ)/p := by dsimp [N]; linarith only [hd,hl]
  have h₂ : (N : ℝ)/p ≤ z.right.value := by dsimp [N]; linarith only [hd,hu]
  have hm (v) : w.count v ≤ p^2 := ((w.cap v).trans (C.toRowData.scan_le_ceiling t v)).trans hsq.le
  have h := selected_strip_prime_cost C.toRowData w z.left z.right hc.left_den hc.right_den p hp δ hd.le
    hl hu hw hm z.boxes hc.boxes_ok
  apply C.toPrimeShapeData.finite_residue w p _ h
  have ho := (checked_strips s z.left z.right hc.left_den hc.right_den h₁ h₂ ⟨0,0⟩ z.boxes hc.boxes_ok).1
  calc
    _ ≤ (z.boxes.map Box.gain).sum*p := latticeSaving_upper z.boxes N p hp.pos ⟨0,0⟩ (by simp [Boundary.value]) ho
    _ ≤ 10*N := Nat.mul_le_mul (C.gain_cap z hz) hpn
    _ = (10*s.massUnit)*t := by unfold N; ring
    _ ≤ baseCoefficient s*t := Nat.mul_le_mul_right t C.enough
    _ ≤ _ := Nat.le_add_right _ _

noncomputable def localTail (s : Shape) (cuts : List ℚ) (N p : ℕ) : ℝ :=
  ∑ u ∈ activeLevels cuts s.largestRowQ N p, (N : ℝ)*(s.totalWidthQ : ℝ)*s.netTailValue (u+1) ((p : ℝ)/N)

def localSmallCost (s : Shape) (t p : ℕ) :=
  if p^2 ≤ primeCeiling s t then p.log (primeCeiling s t)*layerTotal s t else 0

def primeBaseline (s : Shape) (g : List (List ℤ)) (K t L : ℕ) :=
  primeBase s g K t+L*rowPadding s g

theorem PrimeCertificate.local_ledger (C : PrimeCertificate s g K T cuts slabs) :
    ∀ᶠ t : ℕ in atTop, ∀ (a b : ℕ) (y : ℂ) (w : SelectedPolynomial s g t y a b) (p : ℕ), p.Prime →
      (w.denominator.factorization p : ℝ) + localTail s cuts (s.massUnit*t) p + (residueReward slabs s K t p : ℝ) ≤
      (primeBaseline s g K t cuts.length : ℝ) + (localSmallCost s t p : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),eventually_prime_square s C.mass_pos T] with t ht hsq a b y w p hp
  let N := s.massUnit*t
  let H := activeLevels cuts s.largestRowQ N p
  have hH (u : ℕ) (hu : u ∈ H) : N < T*p :=
    (C.cut_prime_bounds (mem_range.mp (mem_filter.mp hu).1) (mem_filter.mp hu).2).1
  have noH (hn : ¬ N < T*p) : localTail s cuts N p = 0 := by
    have he : H = ∅ := eq_empty_iff_forall_notMem.mpr (fun u hu => hn (hH u hu))
    change ∑ u ∈ H, _ = 0
    rw [he,sum_empty]
  have hb : primeBase s g K t ≤ primeBaseline s g K t cuts.length := Nat.le_add_right _ _
  have hs (v) := (w.cap v).trans (C.toRowData.scan_le_ceiling t v)
  rcases residueReward_single slabs s K t p ⟨T,1⟩ Nat.zero_lt_one C.slabs_ok with hzero|⟨z,hz,he,hr⟩
  · rw [hzero,Nat.cast_zero,add_zero]
    by_cases hsmall : p^2 ≤ primeCeiling s t
    · have ht0 := noH (fun hh => hsmall.not_gt (hsq p hp.pos hh.le).2)
      have hc := w.small_cost (primeCeiling s t) p hp (fun i => (w.rowIndex i).2.isLt.le.trans (hs _))
      rw [w.layer_sum] at hc
      rw [ht0,add_zero,localSmallCost,if_pos hsmall]
      exact (show (w.denominator.factorization p : ℝ) ≤ ((p.log (primeCeiling s t)*layerTotal s t : ℕ) : ℝ) by exact_mod_cast hc).trans
        (le_add_of_nonneg_left (Nat.cast_nonneg _))
    · have hlarge : primeCeiling s t < p^2 := Nat.lt_of_not_ge hsmall
      have hp2 : p ≠ 2 := by
        intro he
        subst p
        have hh := C.pad_four
        unfold primeCeiling at hlarge
        omega
      have hc := C.toPrimeShapeData.finite_levels w ht p hp hp2 (fun v => (hs v).trans hlarge.le) H
      have hn := activeLevels_card cuts s.largestRowQ N p
      have hpad : (H.card : ℝ)*(rowPadding s g : ℝ) ≤ (cuts.length : ℝ)*rowPadding s g :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Nat.cast_nonneg _)
      rw [localSmallCost,if_neg hsmall,Nat.cast_zero,add_zero,primeBaseline,Nat.cast_add,Nat.cast_mul]
      exact hc.trans (add_le_add le_rfl hpad)
  · have ht0 := noH (C.residue_beyond_split hz he).not_gt
    have hc := (C.eligible_cost w hp hz he).trans hb
    rw [hr,ht0,add_zero]
    have hc' : (w.denominator.factorization p : ℝ) + (latticeSaving z.boxes N p : ℝ) ≤
        primeBaseline s g K t cuts.length := by exact_mod_cast hc
    exact hc'.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

end PiPolynomialValues.FourPeriod
