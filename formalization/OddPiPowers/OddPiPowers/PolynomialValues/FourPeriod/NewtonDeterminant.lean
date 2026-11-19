module

public import OddPiPowers.PolynomialValues.FourPeriod.NewtonRows
public import OddPiPowers.PolynomialValues.FourPeriod.MonicRows
public import OddPiPowers.PolynomialValues.FourPeriod.PrimeDeterminant

/-! Explicit prime-power divisibility of the actual raw determinant for
every prime, using step-one monic Newton polynomials on each full prefix. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset Polynomial

theorem entryWithRow_dvd_of_derivatives (g : GaussianInt) (v t : ℤ) (j : ℕ) (f : GaussianInt[X])
    (h : ∀ k ≤ j, g ∣ ((derivative^[k]) f).eval (t : GaussianInt)) :
    C g ∣ entryWithRow v t j f := by
  induction j generalizing f with
  | zero =>
    have hd := map_dvd (C : GaussianInt →+* GaussianInt[X]) (h 0 (by decide))
    change C g ∣ C (f.eval (t : GaussianInt)) at hd
    simpa only [entryWithRow,AddMonoidHom.coe_mk,ZeroHom.coe_mk,rowOperator,eval_map_apply] using
      dvd_mul_of_dvd_right hd (C (phase (v*t)))
  | succ j ih =>
    rw [entryWithRow_succ]
    apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply ih f.derivative
      intro k hk
      simpa only [Function.iterate_succ_apply] using h (k+1) (Nat.succ_le_succ hk)
    · exact dvd_mul_of_dvd_right (ih f (fun k hk => h k (Nat.le_succ_of_le hk))) _

noncomputable def gaussianNewton (step : ℕ) (a : ℤ) (m : ℕ) : GaussianInt[X] :=
  (newtonRow step a m).map (Int.castRingHom GaussianInt)

theorem gaussianNewton_monic (step m : ℕ) (a : ℤ) : (gaussianNewton step a m).Monic :=
  (newtonRow_monic _ _ _).map _

theorem gaussianNewton_degree (step m : ℕ) (a : ℤ) : (gaussianNewton step a m).natDegree = m :=
  ((newtonRow_monic _ _ _).natDegree_map _).trans (newtonRow_degree _ _ _)

theorem newton_entry_dvd (p step m L j : ℕ) (a t v : ℤ) (hp : p.Prime)
    (hc : step.Coprime p) (hL : p.log m ≤ L) :
    (C (p : GaussianInt))^(m.factorial.factorization p-L*j) ∣
      entryWithRow v t j (gaussianNewton step a m) := by
  rw [← map_pow]
  apply entryWithRow_dvd_of_derivatives
  intro k hk
  have he := newtonRow_prime_derivative p step m L k a t hp hc hL
  have hk' := Nat.mul_le_mul_left L hk
  have hd := (pow_dvd_pow (p : ℤ) (by omega :
    m.factorial.factorization p-L*j ≤ m.factorial.factorization p-L*k)).trans he
  have hg := map_dvd (Int.castRingHom GaussianInt) hd
  unfold gaussianNewton
  rw [iterate_derivative_map]
  change _ ∣ (Polynomial.map (Int.castRingHom GaussianInt) ((derivative^[k]) (newtonRow step a m))).eval
    ((Int.castRingHom GaussianInt) t)
  rw [eval_map_apply]
  simpa only [map_pow,map_natCast] using hg

theorem rawDeterminant_prime_dvd {V n : ℕ} {m : Fin V → ℕ} (e : Fin n ≃ RowCandidates m)
    (node : Fin V → ℤ) (cols : Fin n → ℤ × ℕ) (p L : ℕ) (hp : p.Prime)
    (hL : ∀ i, p.log (e i).2.val ≤ L) :
    let rows := fun i => (node (e i).1,(e i).2.val)
    C ((p^((rowFactorial rows).factorization p - L*(∑ j, (cols j).2)) : ℕ) : GaussianInt) ∣
      rawDeterminant rows cols := by
  let f (i) := gaussianNewton 1 0 (e i).2.val
  let rows := fun i => (node (e i).1,(e i).2.val)
  let A := rowPolynomialMatrix e node cols f
  have hdeg (i) : (f i).natDegree = (e i).2.val := gaussianNewton_degree _ _ _
  have hA : A.det = rawDeterminant rows cols :=
    rowPolynomialMatrix_det e node cols f (fun i => (hdeg i).le) (fun i => by
      rw [← hdeg i,coeff_natDegree]
      exact gaussianNewton_monic _ _ _)
  have hd := pow_dvd_det_of_entry_loss (C (p : GaussianInt)) A
    (fun i => (e i).2.val.factorial.factorization p) (fun j => L*(cols j).2)
    (fun i j => newton_entry_dvd p 1 _ L (cols j).2 0 (cols j).1 (node (e i).1) hp
      (Nat.coprime_one_left _) (hL i))
  change C ((p^((rowFactorial rows).factorization p - L*(∑ j, (cols j).2)) : ℕ) : GaussianInt) ∣ _
  rw [← hA,rowFactorial_factorization,Nat.cast_pow,map_pow,mul_sum]
  exact hd

end PiPolynomialValues.FourPeriod
