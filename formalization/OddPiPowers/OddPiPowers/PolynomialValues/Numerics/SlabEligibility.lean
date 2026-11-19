module

public import OddPiPowers.PolynomialValues.Numerics.ActualStripSaving
public import OddPiPowers.PolynomialValues.Numerics.PrimeBoxPrimeSum

/-! Every prime in a fixed, trimmed reciprocal window is eventually
large enough for all prefixes of every possible selected minor. -/

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod Filter Finset

variable {s : Shape} {g : List (List ℤ)} {K : ℕ}

theorem RowData.eventually_window_primes (D : RowData s g K) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℕ in atTop, ∀ p : ℕ, 0 < p → s.massUnit*t ≤ T*p →
      (∀ i ∈ s.rows, (K : ℝ) < rowRate s i*δ*p) ∧
      ∀ v, scanRowCount s t (scannedNode g v) ≤ p^2 := by
  obtain ⟨q,hq⟩ := exists_nat_gt ((K : ℝ)*s.massUnit/δ)
  let A := ∑ v, shapeRowUnits s g v
  let P := q+A*T+s.widths.length+2
  filter_upwards [eventually_gt_atTop (T*P)] with t ht p hp hN
  have htN : t ≤ s.massUnit*t := by
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ s.massUnit from D.mass_pos)
  have htp := htN.trans hN
  have hP : P < p := by
    by_contra! he
    exact ht.not_ge (htp.trans (Nat.mul_le_mul_left T he))
  have hq' : (q : ℝ) ≤ p := by exact_mod_cast (show q ≤ p by dsimp [P] at hP; omega)
  have hm : (0 : ℝ) < s.massUnit := by exact_mod_cast D.mass_pos
  constructor
  · intro i hi
    have h : (K : ℝ)*s.massUnit < (p : ℝ)*δ := (div_lt_iff₀ hδ).mp (hq.trans_le hq')
    have hh : (K : ℝ) < (1/(s.massUnit : ℝ))*δ*p := by
      rw [show 1/(s.massUnit : ℝ)*δ*p = (p*δ)/s.massUnit by ring]
      exact (lt_div_iff₀ hm).mpr h
    have hunit : (1 : ℝ) ≤ s.rowUnits i := by exact_mod_cast D.row_pos i hi
    exact hh.trans_le (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hunit hm.le) hδ.le) (Nat.cast_nonneg p))
  · intro v
    have ha : shapeRowUnits s g v ≤ A := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    have he : scanRowCount s t (scannedNode g v) = shapeRowUnits s g v*t+(s.widths.length+1) := by
      unfold scanRowCount shapeRowUnits
      ring
    have hpad : s.widths.length+1 ≤ (s.widths.length+1)*p := by
      simpa using Nat.mul_le_mul_left (s.widths.length+1) hp
    have hcoef : A*T+(s.widths.length+1) ≤ p := by dsimp [P] at hP; omega
    calc
      _ = _ := he
      _ ≤ A*(T*p)+(s.widths.length+1)*p := Nat.add_le_add (Nat.mul_le_mul ha htp) hpad
      _ = (A*T+(s.widths.length+1))*p := by ring
      _ ≤ p^2 := by simpa only [pow_two] using Nat.mul_le_mul_right p hcoef

theorem eventually_selected_window_cost (D : RowData s g K) (W : OddPiPowers.PrimeRates.PrimeWindow)
    (l u : Abscissa) (hl : 0 < l.den) (hu : 0 < u.den) {δ : ℝ} (hδ : 0 < δ)
    (hlo : l.value+δ ≤ W.lower) (hhi : W.upper ≤ u.value-δ)
    (bs : List Box) (hbs : boxesPass s l u ⟨0,0⟩ bs = true) :
    ∀ᶠ t : ℕ in atTop, ∀ (a b : ℕ) (y : ℂ) (w : SelectedPolynomial s g t y a b),
      ∀ p ∈ W.primes (s.massUnit*t), w.denominator.factorization p ≤
        (∑ j, (w.cols j).2) - nodePairOrder (scannedNode g) w.count - latticeSaving bs (s.massUnit*t) p := by
  obtain ⟨T,hT⟩ := exists_nat_gt W.upper
  filter_upwards [D.eventually_window_primes T hδ] with t ht a b y w p hp
  have hprime := ((W.mem_primes _ _).mp hp).1
  obtain ⟨ha,hb⟩ := (W.mem_primes_quotient _ _ hprime).mp hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hmul := (div_le_iff₀ hp').mp (hb.trans hT).le
  have hc := ht p hprime.pos (by exact_mod_cast hmul)
  exact selected_strip_prime_cost D w l u hl hu p hprime δ hδ.le (hlo.trans ha) (hb.le.trans hhi)
    hc.1 (fun v => (w.cap v).trans (hc.2 v)) bs hbs

end PiPolynomialValues.PrimeWindow
