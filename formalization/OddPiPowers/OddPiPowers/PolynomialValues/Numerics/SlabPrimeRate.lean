module

public import OddPiPowers.PolynomialValues.Numerics.TrimmedBoxRate
public import OddPiPowers.PolynomialValues.Numerics.SlabRewards
public import OddPiPowers.PolynomialValues.Numerics.ActiveTailLevels

/-! Every checked slab attains its full rational credit in the lower
limit of the actual large-prime sum, uniformly over the selected minor. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Finset Filter MeasureTheory
open scoped Topology Interval

theorem slab_credit_le_area {s : Shape} {z : Slab} {floor : ℝ} (hc : z.Checked s floor)
    (hs : 0 < s.widths.sum) :
    (z.credit : ℝ)/creditScale*(s.totalWidthQ : ℝ) ≤ stripAreaSum z.boxes z.left.value z.right.value := by
  have hp := (checked_strips s z.left z.right hc.left_den hc.right_den le_rfl
    hc.interior.le ⟨0,0⟩ z.boxes hc.boxes_ok).2
  have hT : 0 < (s.totalWidthQ : ℝ) := by
    have hh : 0 < s.totalWidthQ := div_pos (mul_pos (by norm_num) (by exact_mod_cast hs)) (by norm_num)
    exact_mod_cast hh
  have hf (b : Box) (hb : b ∈ z.boxes) : (b.credit : ℝ)/creditScale*(s.totalWidthQ : ℝ) ≤
      (2*b.gain : ℝ)*(∫ y in z.right.value⁻¹..z.left.value⁻¹, stripWidth b y) := by
    have h := mul_le_mul_of_nonneg_right (credit_le_gain_mul_area s z.left z.right b hs
      hc.left_num hc.right_num (hp b hb).2) hT.le
    apply h.trans_eq
    have ht : (s.totalWidthQ : ℝ) = 2*(s.widths.sum : ℝ)/10000 := by
      simp only [Shape.totalWidthQ,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    unfold weightedArea
    rw [← ht]
    field_simp [hT.ne'] <;> ring
  have hl (bs : List Box) (hbs : ∀ b ∈ bs, b ∈ z.boxes) :
      (((bs.map Box.credit).sum : ℕ) : ℝ)/creditScale*(s.totalWidthQ : ℝ) ≤
        stripAreaSum bs z.left.value z.right.value := by
    induction bs with
    | nil => simp [stripAreaSum]
    | cons b bs ih =>
      have hr := ih (fun v hv => hbs v (List.mem_cons_of_mem _ hv))
      have h := hf b (hbs b (by simp))
      simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div,add_mul]
      exact add_le_add h hr
  exact hl z.boxes (fun _ h => h)

noncomputable def slabPrimeRate (s : Shape) (K : ℕ) (z : Slab) (t : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE (primeCeiling s t), (z.reward s K t p : ℝ)*Real.log p)/((s.massUnit*t : ℕ) : ℝ)^2

noncomputable def residuePrimeRate (s : Shape) (K : ℕ) (xs : List Slab) (t : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE (primeCeiling s t), (residueReward xs s K t p : ℝ)*Real.log p)/((s.massUnit*t : ℕ) : ℝ)^2

theorem window_le_slab_eventually {s : Shape} {g : List (List ℤ)} {K : ℕ}
    (D : RowData s g K) (hmax : s.massUnit ≤ maxRowUnits s) (z : Slab) (W : OddPiPowers.PrimeRates.PrimeWindow)
    (δ : ℝ) (hd : 0 < δ) (hl : z.left.value+δ ≤ W.lower) (hr : W.upper ≤ z.right.value-δ) (hone : 1 ≤ W.lower) :
    ∀ᶠ t : ℕ in atTop, windowLatticeRate W z.boxes (s.massUnit*t) ≤ slabPrimeRate s K z t := by
  classical
  obtain ⟨T,hT⟩ := exists_nat_gt W.upper
  filter_upwards [D.eventually_window_primes T hd,eventually_prime_square s D.mass_pos T] with t ha hb
  let N := s.massUnit*t
  have hm (p : ℕ) (hp : p ∈ W.primes N) : z.Eligible s K t p ∧ p ∈ Nat.primesLE (primeCeiling s t) := by
    have hprime := ((W.mem_primes _ _).mp hp).1
    obtain ⟨h₁,h₂⟩ := (W.mem_primes_quotient _ _ hprime).mp hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hNp : N ≤ T*p := by exact_mod_cast (div_le_iff₀ hp').mp (h₂.trans hT).le
    have hbig := hb p hprime.pos hNp
    have hsmall := (ha p hprime.pos hNp).1
    have hup : p ≤ N := by
      have h := (le_div_iff₀ hp').mp (hone.trans h₁)
      simpa only [one_mul,Nat.cast_le] using h
    refine ⟨⟨hbig.1,hbig.2,δ,hd,hl.trans h₁,h₂.le.trans hr,hsmall⟩,Nat.mem_primesLE.mpr ⟨?_,hprime⟩⟩
    exact hup.trans ((Nat.mul_le_mul_right t hmax).trans (Nat.le_add_right _ _))
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ = ∑ p ∈ W.primes N, (z.reward s K t p : ℝ)*Real.log p := by
      apply sum_congr rfl
      intro p hp
      rw [Slab.reward,if_pos (hm p hp).1]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun p hp => (hm p hp).2) (fun p hp _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)))

theorem slab_prime_rate {s : Shape} {g : List (List ℤ)} {K : ℕ} (D : RowData s g K)
    (hmax : s.massUnit ≤ maxRowUnits s) (hs : 0 < s.widths.sum) {z : Slab} {floor : ℝ}
    (hc : z.Checked s floor) (hone : 1 ≤ floor) :
    LowerRate (slabPrimeRate s K z) ((z.credit : ℝ)/creditScale*(s.totalWidthQ : ℝ)) := by
  intro ε hε
  have hl : 0 < z.left.value := (zero_lt_one.trans_le hone).trans_le hc.starts
  obtain ⟨δ,W,hd,h₁,h₂,hprice⟩ := exists_trimmed_window z.boxes hl hc.interior (show 0 < ε/2 by positivity)
  have he := ((window_lattice_rate W z.boxes).comp (massScale_tendsto s D.mass_pos)).mono
    (window_le_slab_eventually D hmax z W δ hd h₁.ge h₂.le (by rw [h₁]; linarith only [hone,hc.starts,hd]))
  have hfull := slab_credit_le_area hc hs
  filter_upwards [he (ε/2) (by positivity)] with t ht
  linarith only [hfull,hprice,ht]

theorem all_slabs_prime_rate {s : Shape} {g : List (List ℤ)} {K : ℕ} (D : RowData s g K)
    (hmax : s.massUnit ≤ maxRowUnits s) (hs : 0 < s.widths.sum) (xs : List Slab)
    (prev : Abscissa) (hp : 0 < prev.den) (hone : 1 ≤ prev.value) (hx : slabsPass s prev xs = true) :
    LowerRate (residuePrimeRate s K xs) ((((xs.map Slab.credit).sum : ℕ) : ℝ)/creditScale*(s.totalWidthQ : ℝ)) := by
  induction xs generalizing prev with
  | nil =>
    intro ε hε
    exact Eventually.of_forall (fun n => by simp [residuePrimeRate,residueReward,hε.le])
  | cons z xs ih =>
    simp only [slabsPass,Bool.and_eq_true] at hx
    have hc := Slab.checked_of_valid hp hx.1
    have ht := ih z.right hc.right_den ((hone.trans hc.starts).trans hc.interior.le) hx.2
    have ha := (slab_prime_rate D hmax hs hc hone).add ht
    simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_div,add_mul]
    apply ha.mono
    apply Eventually.of_forall
    intro t
    have he (p : ℕ) : (residueReward (z::xs) s K t p : ℝ) = (z.reward s K t p : ℝ)+(residueReward xs s K t p : ℝ) := by
      simp [residueReward]
    unfold residuePrimeRate slabPrimeRate
    simp only [he,add_mul,sum_add_distrib,add_div,le_refl]

end PiPolynomialValues.PrimeWindow
