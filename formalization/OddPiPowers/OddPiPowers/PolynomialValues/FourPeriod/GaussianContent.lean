module

public import OddPiPowers.PolynomialValues.FourPeriod.IntegerMatrix
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Factorization.Basic

/-! Remove the common rational-integer factor of both coordinates of
every Gaussian coefficient, including after a power of X has been removed. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

def gaussianContent (q : GaussianInt[X]) : ℕ :=
  q.support.gcd (fun i => Nat.gcd (q.coeff i).re.natAbs (q.coeff i).im.natAbs)

theorem nat_dvd_gaussian_iff (g : ℕ) (a : GaussianInt) :
    (g : GaussianInt) ∣ a ↔ g ∣ a.re.natAbs ∧ g ∣ a.im.natAbs := by
  constructor
  · rintro ⟨b,rfl⟩
    constructor
    · apply Int.natCast_dvd.mp
      exact ⟨b.re,by simp [Zsqrtd.re_mul]⟩
    · apply Int.natCast_dvd.mp
      exact ⟨b.im,by simp [Zsqrtd.im_mul]⟩
  · rintro ⟨hr,hi⟩
    obtain ⟨x,hx⟩ := Int.natCast_dvd.mpr hr
    obtain ⟨y,hy⟩ := Int.natCast_dvd.mpr hi
    refine ⟨⟨x,y⟩,Zsqrtd.ext ?_ ?_⟩
    · simpa [Zsqrtd.re_mul] using hx
    · simpa [Zsqrtd.im_mul] using hy

theorem dvd_gaussianContent_iff (g : ℕ) (q : GaussianInt[X]) :
    g ∣ gaussianContent q ↔ C (g : GaussianInt) ∣ q := by
  rw [gaussianContent, Finset.dvd_gcd_iff, C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    by_cases hi : i ∈ q.support
    · exact (nat_dvd_gaussian_iff _ _).mpr ⟨(h i hi).trans (Nat.gcd_dvd_left _ _),
        (h i hi).trans (Nat.gcd_dvd_right _ _)⟩
    · rw [notMem_support_iff.mp hi]
      exact dvd_zero _
  · intro h i _
    have hh := (nat_dvd_gaussian_iff _ _).mp (h i)
    exact Nat.dvd_gcd hh.1 hh.2

theorem C_dvd_strip_origin (g : ℕ) (k : ℕ) (q : GaussianInt[X]) :
    C (g : GaussianInt) ∣ X^k*q ↔ C (g : GaussianInt) ∣ q := by
  constructor
  · intro h
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    rw [← coeff_X_pow_mul q k i]
    exact (C_dvd_iff_dvd_coeff _ _).mp h _
  · exact fun h => dvd_mul_of_dvd_right h _

def commonDenominator (F : ℕ) (q : GaussianInt[X]) : ℕ := F / Nat.gcd F (gaussianContent q)

theorem commonDenominator_split (F : ℕ) (q : GaussianInt[X]) :
    commonDenominator F q * Nat.gcd F (gaussianContent q) = F :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

theorem commonDenominator_pos {F : ℕ} (hF : 0 < F) (q : GaussianInt[X]) :
    0 < commonDenominator F q := by
  have h := commonDenominator_split F q
  by_contra! hn
  rw [Nat.le_zero.mp hn,zero_mul] at h
  omega

theorem commonDenominator_prime_bound {F p E : ℕ} (hp : p.Prime) (hF : F ≠ 0)
    (q : GaussianInt[X]) (h : C ((p^(F.factorization p-E) : ℕ) : GaussianInt) ∣ q) :
    (commonDenominator F q).factorization p ≤ E := by
  let g := Nat.gcd F (gaussianContent q)
  have hg : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hF)).ne'
  have hd : p^(F.factorization p-E) ∣ g := Nat.dvd_gcd
    ((hp.pow_dvd_iff_le_factorization hF).mpr (Nat.sub_le _ _)) ((dvd_gaussianContent_iff _ _).mpr h)
  have he := (hp.pow_dvd_iff_le_factorization hg).mp hd
  change (F/g).factorization p ≤ E
  rw [Nat.factorization_div (Nat.gcd_dvd_left _ _), Finsupp.coe_tsub, Pi.sub_apply]
  change F.factorization p - g.factorization p ≤ E
  omega

end PiPolynomialValues.FourPeriod
