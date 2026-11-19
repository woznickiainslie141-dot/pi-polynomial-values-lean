module

public import OddPiPowers.PolynomialValues.Analysis.AtomicPotential
public import OddPiPowers.PolynomialValues.Analysis.RadialChordError
public import OddPiPowers.PolynomialValues.Analysis.VandermondeNorm

/-! The actual integer-frequency product is bounded by the radial energy
of its normalized atomic distribution, uniformly at repeated nodes. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Real
open scoped ComplexConjugate

theorem sum_frequencyPairs_symm {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hs : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) = 2*(∑ e ∈ frequencyPairs n, F e.1 e.2)+∑ i, F i i := by
  let H (i j : Fin n) := if i<j then F i j else 0
  have h (i j : Fin n) : F i j = H i j+H j i+(if j=i then F i i else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [H,h,h.not_gt,h.ne']
    · subst j; simp [H]
    · simp [H,h,h.not_gt,h.ne,hs i j]
  have he : (∑ e ∈ frequencyPairs n, F e.1 e.2) = ∑ i, ∑ j, H i j := by
    rw [frequencyPairs,sum_filter,sum_product]
  have hd : (∑ i, ∑ j : Fin n, if j=i then F i i else 0) = ∑ i, F i i := by simp
  calc
    _ = ∑ i, ∑ j, (H i j+H j i+(if j=i then F i i else 0)) := by
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl (fun j _ => h i j)
    _ = _ := by
      simp only [sum_add_distrib,hd,he]
      rw [show (∑ i, ∑ j, H j i) = ∑ i, ∑ j, H i j from sum_comm]
      ring

theorem radialPair_log_comm {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : log (radialPair r u v) = log (radialPair r v u) :=
  (log_radial_pair_hasSum hr hr1 hu hv).unique
    ((log_radial_pair_hasSum hr hr1 hv hu).congr_fun (fun _ => by ring))

theorem diagonal_radial_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {u : ℂ}
    (hu : ‖u‖ = 1) : 2*log (1-r) ≤ log (radialPair r u u) := by
  have hs (z : ℂ) (hz : ‖z‖ = 1) : 1-r ≤ ‖1-(r : ℂ)*z‖ := by
    simpa [norm_mul,hz,abs_of_nonneg hr] using norm_sub_norm_le (1 : ℂ) ((r : ℂ)*z)
  have hp : (1-r)^2 ≤ radialPair r u u := by
    rw [sq]
    exact mul_le_mul (hs _ (by simp [norm_mul,hu])) (hs _ (by simp [norm_mul,hu]))
      (sub_nonneg.mpr hr1.le) (norm_nonneg _)
  simpa only [log_pow,Nat.cast_ofNat] using log_le_log (sq_pos_of_pos (sub_pos.mpr hr1)) hp

theorem empirical_pair_bound {n : ℕ} (x : Fin n → ℤ) (y : Fin n → FrequencyInterval) {N r : ℝ}
    (hN : 0 < N) (hr : 0 < r) (hr1 : r < 1) (hx : ∀ i, (x i : ℝ) = N*(y i : ℝ)) :
    let μ := atomicCharge y (fun _ => N⁻¹)
    let c := 1/r+(4/N)/(1-r)^2
    log (pairEnvelope x) ≤ ((frequencyPairs n).card : ℝ)*(log (N/2)+log c) +
      (N^2*radialInteraction unitFrequency r μ μ-(n : ℝ)*(2*log (1-r)))/2 := by
  let F (i j : Fin n) := log (radialPair r (unitFrequency (y j)) (unitFrequency (y i)))
  let c := 1/r+(4/N)/(1-r)^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hpair (i j : Fin n) :
      log (‖((x j-x i : ℤ) : ℂ)‖+2) ≤ log (N/2)+log c+F i j := by
    have hreg := regularized_pair_bound (unitFrequency_norm (y j)) (unitFrequency_norm (y i)) hr hr1
      (ε := 2/N) (by positivity)
    rw [unitFrequency_re,unitFrequency_re] at hreg
    have hnum : ‖((x j-x i : ℤ) : ℂ)‖+2 =
        (N/2)*(2*(|(y j : ℝ)-y i|+2/N)) := by
      rw [Complex.norm_intCast,Int.cast_sub,hx,hx,← mul_sub,abs_mul,abs_of_pos hN]
      field_simp
    have hfactor : 1/r+2*(2/N)/(1-r)^2 = c := by dsimp [c]; ring
    rw [hfactor] at hreg
    have H := log_le_log (show 0 < ‖((x j-x i : ℤ) : ℂ)‖+2 by positivity)
      (hnum.le.trans (mul_le_mul_of_nonneg_left hreg (by positivity)))
    rw [log_mul (by positivity) (mul_pos hc (radialPair_pos hr.le hr1 (unitFrequency_norm _) (unitFrequency_norm _))).ne',
      log_mul hc.ne' (radialPair_pos hr.le hr1 (unitFrequency_norm _) (unitFrequency_norm _)).ne'] at H
    dsimp [F]
    linarith
  have H := sum_le_sum (s := frequencyPairs n) (fun e _ => hpair e.1 e.2)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at H
  have hs := sum_frequencyPairs_symm F (fun i j => radialPair_log_comm hr.le hr1 (unitFrequency_norm _) (unitFrequency_norm _))
  have hd := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => diagonal_radial_lower hr.le hr1 (unitFrequency_norm (y i)))
  change (∑ _i : Fin n, 2*log (1-r)) ≤ ∑ i, F i i at hd
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hd
  let μ := atomicCharge y (fun _ => N⁻¹)
  have hμ : N^2*radialInteraction unitFrequency r μ μ = ∑ i, ∑ j, F i j := by
    rw [show radialInteraction unitFrequency r μ μ = _ from
      atomicInteraction_eq unitFrequency unitFrequency_norm hr.le hr1 y y (fun _ => N⁻¹) (fun _ => N⁻¹)]
    simp only [← mul_sum]
    dsimp [F]
    field_simp
  dsimp only
  change log (pairEnvelope x) ≤ _ + (N^2*radialInteraction unitFrequency r μ μ-_)/2
  rw [pairEnvelope,log_prod (fun _ _ => by positivity),hμ]
  change _ ≤ ((frequencyPairs n).card : ℝ)*(log (N/2)+log c)+_
  linarith

end PiPolynomialValues.FourPeriod
