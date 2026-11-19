module

public import OddPiPowers.PolynomialValues.FourPeriod.EntryDifference
public import OddPiPowers.PolynomialValues.FourPeriod.EntryCoefficients

/-! At every odd prime with square larger than the row index, each
actual differenced coefficient satisfies both independent loss bounds. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial Finset

noncomputable def differencedKernel (a r t : ℤ) (j σ k h : ℕ) : GaussianInt :=
  (((σ.descFactorial k : ℕ) : GaussianInt)*4^k) *
    commonEntryCoeff r t j h (gaussianNewton 4 a (σ-k))

theorem differenced_entry_coefficient (a v t : ℤ) (j σ k h : ℕ) :
    (((fwdDiff (4 : ℤ))^[k]) (fun u => entryWithRow v u j (gaussianNewton 4 a σ)) t).coeff h =
      (v : GaussianInt)^h * differencedKernel a (v%4) t j σ k h := by
  rw [differenced_newton_entry,coeff_C_mul,entryWithRow_coeff_factor,differencedKernel]
  ring

theorem differencedKernel_support {a r t : ℤ} {j σ k h : ℕ}
    (hn : differencedKernel a r t j σ k h ≠ 0) : k ≤ σ ∧ h ≤ j := by
  constructor
  · by_contra! he
    exact hn (by simp [differencedKernel,Nat.descFactorial_of_lt he])
  · by_contra! he
    exact hn (by simp [differencedKernel,commonEntryCoeff,derivativeWeight_zero he])

theorem factorial_large (p s : ℕ) (hp : p.Prime) (hs : s < p^2) :
    s.factorial.factorization p = s/p := by
  have hl : Nat.log p s < 2 := Nat.log_lt_of_lt_pow' (by decide) hs
  rw [Nat.factorization_factorial hp hl]
  rw [show Ico 1 2 = ({1} : Finset ℕ) from by decide]
  simp

private theorem gaussianNewton_prime_derivative (p m ℓ : ℕ) (a t : ℤ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : m < p^2) :
    (p : GaussianInt)^(m/p-ℓ) ∣ ((derivative^[ℓ]) (gaussianNewton 4 a m)).eval (t : GaussianInt) := by
  have h₄ : Nat.Coprime 4 p := (hp.odd_of_ne_two hp2).coprime_two_left.pow_left 2
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow' (by decide) hm
  have hd := newtonRow_prime_derivative p 4 m 1 ℓ a t hp h₄ (by omega)
  rw [factorial_large p m hp hm,one_mul] at hd
  let φ := Int.castRingHom GaussianInt
  have hh := map_dvd φ hd
  change _ ∣ ((derivative^[ℓ]) ((newtonRow 4 a m).map φ)).eval (φ t)
  rw [iterate_derivative_map,eval_map_apply]
  simpa only [map_pow,map_natCast] using hh

theorem differencedKernel_prime_power (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a r t : ℤ) (j σ k h : ℕ) (hs : σ < p^2) :
    (p : GaussianInt)^(σ/p - min (j-h) (σ/p-k/p)) ∣ differencedKernel a r t j σ k h := by
  by_cases hk : k ≤ σ
  · let D := (σ.descFactorial k).factorization p
    have hdf : σ.descFactorial k ≠ 0 := fun hz => (Nat.descFactorial_eq_zero_iff_lt.mp hz).not_ge hk
    have hsum : (σ-k)/p + D = σ/p := by
      have hh := congrArg (fun m : ℕ => m.factorization p) (Nat.factorial_mul_descFactorial hk)
      simpa only [Nat.factorization_mul (Nat.factorial_ne_zero _) hdf,Finsupp.coe_add,Pi.add_apply,
        factorial_large _ _ hp ((Nat.sub_le _ _).trans_lt hs),factorial_large _ _ hp hs,D] using hh
    have hfloor : (σ-k)/p + k/p ≤ σ/p := by
      have hh : (σ-k)/p + k/p ≤ ((σ-k)+k)/p := Nat.div_add_div_le_add_div
      rwa [Nat.sub_add_cancel hk] at hh
    have hd : (p : GaussianInt)^D ∣ ((σ.descFactorial k : ℕ) : GaussianInt) := by
      have hnat := (hp.pow_dvd_iff_le_factorization hdf).mpr (le_refl D)
      have hcast : ((p^D : ℕ) : GaussianInt) ∣ ((σ.descFactorial k : ℕ) : GaussianInt) :=
        map_dvd (Nat.castRingHom GaussianInt) hnat
      simpa only [Nat.cast_pow] using hcast
    have he := gaussianNewton_prime_derivative p (σ-k) (j-h) a t hp hp2 ((Nat.sub_le _ _).trans_lt hs)
    have hg : (p : GaussianInt)^((σ-k)/p-(j-h)) ∣ commonEntryCoeff r t j h (gaussianNewton 4 a (σ-k)) :=
      dvd_mul_of_dvd_right he _
    have hf := mul_dvd_mul (dvd_mul_of_dvd_left hd ((4 : GaussianInt)^k)) hg
    rw [← pow_add] at hf
    exact (pow_dvd_pow (p : GaussianInt) (by omega :
      σ/p - min (j-h) (σ/p-k/p) ≤ D+((σ-k)/p-(j-h)))).trans hf
  · have hh : σ < k := by omega
    simp [differencedKernel,Nat.descFactorial_of_lt hh]

end PiPolynomialValues.FourPeriod
