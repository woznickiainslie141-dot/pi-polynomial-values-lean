module

public import OddPiPowers.PolynomialValues.Numerics.PrimeGlobalLedger

/-! The prime number theorem at the padded support and the vanishing
small-prime remainder, both normalized by the actual common mass scale. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Filter PrimeWindow OddPiPowers.PrimeRates
open scoped Topology

theorem linear_over_scale (a b u : ℕ) (hu : 0 < u) :
    Tendsto (fun t : ℕ => ((a*t+b : ℕ) : ℝ)/((u*t : ℕ) : ℝ)) atTop (𝓝 ((a : ℝ)/u)) := by
  have h : Tendsto (fun t : ℕ => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds (x := (a : ℝ)/u) (f := atTop (α := ℕ))).add (h.const_mul ((b : ℝ)/u))
  rw [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  push_cast
  field_simp [Nat.cast_ne_zero.mpr ht.ne',Nat.cast_ne_zero.mpr hu.ne'] <;> ring

noncomputable def analyticPrimeBaseline (s : Shape) (g : List (List ℤ)) (K L t : ℕ) : ℝ :=
  let N := s.massUnit*t
  let S := primeCeiling s t
  ((primeBaseline s g K t L : ℝ)*Chebyshev.theta S+Real.sqrt S*(layerTotal s t : ℝ)*Real.log S)/(N : ℝ)^2

variable {s : Shape} {g : List (List ℤ)} {K T : ℕ} {cuts : List ℚ} {slabs : List Slab}

theorem PrimeCertificate.baseline_rate (C : PrimeCertificate s g K T cuts slabs) (L : ℕ) :
    Tendsto (analyticPrimeBaseline s g K L) atTop (𝓝 (((baseCoefficient s : ℕ) : ℝ)/s.massUnit*(s.largestRowQ : ℝ))) := by
  let N (t : ℕ) := s.massUnit*t
  let S (t : ℕ) := primeCeiling s t
  have hSN : Tendsto (fun t => ((S t : ℕ) : ℝ)/(N t : ℝ)) atTop (𝓝 (s.largestRowQ : ℝ)) := by
    simpa only [S,N,primeCeiling,Shape.largestRowQ,Shape.rowMassQ,Rat.cast_div,Rat.cast_natCast,maxRowUnits] using
      linear_over_scale (maxRowUnits s) (s.widths.length+1) s.massUnit C.mass_pos
  have hJN : Tendsto (fun t => (layerTotal s t : ℝ)/(N t : ℝ)) atTop
      (𝓝 ((scaledLayer (shapeBandUnits s) : ℝ)/s.massUnit)) :=
    linear_over_scale _ _ _ C.mass_pos
  have hBN : Tendsto (fun t => (primeBaseline s g K t L : ℝ)/(N t : ℝ)) atTop
      (𝓝 ((baseCoefficient s : ℝ)/s.massUnit)) := by
    simpa only [primeBaseline,primeBase,N,Nat.add_assoc] using
      linear_over_scale (baseCoefficient s) (baseError s g K+L*rowPadding s g) s.massUnit C.mass_pos
  have hinfty : Tendsto S atTop atTop := by
    apply tendsto_atTop.2
    intro q
    filter_upwards [eventually_ge_atTop q] with t ht
    have hmax : 1 ≤ maxRowUnits s := C.mass_pos.trans_le C.ceiling_ge
    have hm := Nat.mul_le_mul_right t hmax
    simp only [one_mul] at hm
    exact ht.trans (hm.trans (Nat.le_add_right _ _))
  have hinfty' : Tendsto (fun t => (S t : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hinfty
  have hθ := (theta_ratio_tendsto.comp hinfty').mul hSN
  have hsmall := ((sqrt_log_over_scale_tendsto.comp hinfty').mul hSN).mul hJN
  have hh := (hBN.mul hθ).add hsmall
  simp only [one_mul,zero_mul,add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  have hs : (S t : ℝ) ≠ 0 := by
    have hz : 0 < S t := by dsimp [S,primeCeiling]; positivity
    exact Nat.cast_ne_zero.mpr hz.ne'
  have hn : (N t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos C.mass_pos ht).ne'
  change ((primeBaseline s g K t L : ℝ)/N t)*(Chebyshev.theta (S t)/S t*((S t : ℝ)/N t))+
    ((Real.sqrt (S t)*Real.log (S t)/S t)*((S t : ℝ)/N t))*((layerTotal s t : ℝ)/N t) =
    ((primeBaseline s g K t L : ℝ)*Chebyshev.theta (S t)+Real.sqrt (S t)*(layerTotal s t : ℝ)*Real.log (S t))/(N t : ℝ)^2
  field_simp [hs,hn] <;> ring

theorem PrimeCertificate.normalized_ledger (C : PrimeCertificate s g K T cuts slabs) :
    ∀ᶠ t : ℕ in atTop, ∀ (a b : ℕ) (y : ℂ) (w : SelectedPolynomial s g t y a b),
      let N := s.massUnit*t
      Real.log (w.denominator : ℝ)/(N : ℝ)^2 + (s.totalWidthQ : ℝ)*aggregateTail s cuts N +
        residuePrimeRate s K slabs t ≤ analyticPrimeBaseline s g K cuts.length t := by
  filter_upwards [C.global_ledger,eventually_gt_atTop (0 : ℕ)] with t hledger ht a b y w
  let N := s.massUnit*t
  let S := primeCeiling s t
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.mul_pos C.mass_pos ht
  have hs : 1 ≤ S := by dsimp [S,primeCeiling]; omega
  have hlog : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast hs)
  have herr := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.nat_sqrt_le_real_sqrt (a := S)) (Nat.cast_nonneg (layerTotal s t))) hlog
  have hd := (hledger a b y w).trans (add_le_add le_rfl herr)
  change Real.log (w.denominator : ℝ)/(N : ℝ)^2+(s.totalWidthQ : ℝ)*aggregateTail s cuts N+
    residuePrimeRate s K slabs t ≤ _/(N : ℝ)^2
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  calc
    _ = Real.log (w.denominator : ℝ)+(N : ℝ)^2*(s.totalWidthQ : ℝ)*aggregateTail s cuts N+
        (N : ℝ)^2*residuePrimeRate s K slabs t := by field_simp [hn.ne'] <;> ring
    _ ≤ _ := hd

end PiPolynomialValues.FourPeriod
