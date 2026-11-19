module

public import OddPiPowers.PolynomialValues.FourPeriod.LocalSymbol
public import OddPiPowers.PolynomialValues.FourPeriod.BandWidth

/-! Count all selected local translation orders against the degree of a
single nonzero polynomial, after clearing each nested bandwidth separately. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial

theorem band_contact_order {ρ : ℂ} (hρ : ρ ≠ 0) (S : Finset ℤ) (p : ℤ → ℂ[X])
    {J : ℕ} (U : ℕ) (B : Fin (J+1) → ℕ) (hB : ∀ k, B k ≤ U)
    (hb : ∀ k, InBand S p k.val (B k)) (hl : ∀ t ∈ S, 0 ≤ t+(U : ℤ))
    (hd : ∀ t ∈ S, (p t).natDegree ≤ J) :
    (exponentialPath ρ (bandMatrix S p B).det).order =
      (wronskianMatrix (fun k : Fin (J+1) => localColumn ρ S p k.val)).det.order := by
  have h := order_symbol_localPath hρ S p U J hl hd
  have hu : IsUnit (exponentialPath ρ (∏ k, (X : ℂ[X])^(U-B k))) := by
    rw [Finset.prod_pow_eq_pow_sum, map_pow]
    apply IsUnit.pow
    change IsUnit (Polynomial.X.eval₂ PowerSeries.C (PowerSeries.C ρ * PowerSeries.exp ℂ))
    rw [eval₂_X]
    exact ((isUnit_iff_ne_zero.mpr hρ).map (PowerSeries.C : ℂ →+* PowerSeries ℂ)).mul
      (PowerSeries.isUnit_exp ℂ)
  rwa [symbolPolynomial_factor S p U B hB hb, map_mul, PowerSeries.order_mul,
    PowerSeries.order_zero_of_isUnit hu, add_zero] at h

theorem selected_contact_sum_le_band {J : ℕ} (S : Finset ℤ) (p : ℤ → ℂ[X])
    (U : ℕ) (B : Fin (J+1) → ℕ) (hB : ∀ k, B k ≤ U)
    (hb : ∀ k, InBand S p k.val (B k)) (hl : ∀ t ∈ S, 0 ≤ t+(U : ℤ))
    (hd : ∀ t ∈ S, (p t).natDegree ≤ J) {t₀ : ℤ} (ht₀ : t₀ ∈ S)
    (hp : p t₀ ≠ 0) (hdeg : (p t₀).natDegree = J)
    (centres : Finset ℂ) (hn : ∀ ρ ∈ centres, ρ ≠ 0)
    (shift : ℂ → Fin (J+1) → ℂ) (hinj : ∀ ρ ∈ centres, Function.Injective (shift ρ))
    (orders : ℂ → Fin (J+1) → ℕ)
    (hvan : ∀ ρ ∈ centres, ∀ i, (PowerSeries.X : PowerSeries ℂ)^(orders ρ i) ∣
      translatedTrajectory ρ (shift ρ i) S p) :
    ∑ ρ ∈ centres, ∑ i, (orders ρ i-J) ≤ ∑ k, 2*B k := by
  have hnz := symbolPolynomial_ne_zero S p U hl hd ht₀ hp hdeg
  have hdet : (bandMatrix S p B).det ≠ 0 := by
    intro h
    exact hnz (by rw [symbolPolynomial_factor S p U B hB hb, h, zero_mul])
  apply (contact_sum_le_degree centres (bandMatrix S p B).det hdet
    (fun ρ => ∑ i, (orders ρ i-J)) hn ?_).trans (bandDeterminant_degree S p B hb)
  intro ρ hρ
  rw [band_contact_order (hn ρ hρ) S p U B hB hb hl hd]
  apply wronskian_order_of_combinations (fun k => localColumn ρ S p k.val)
    (translationMatrix (shift ρ)) (translationMatrix_det_ne_zero _ (hinj ρ hρ)) (orders ρ)
  intro i
  rw [mix_localColumn ρ S p hd]
  exact hvan ρ hρ i

end PiPolynomialValues.FourPeriod
