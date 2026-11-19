module

public import OddPiPowers.PolynomialValues.FourPeriod.RowMultiplicity

/-! Every coefficient of Y to power h is an explicit integral multiple
of one derivative of order j-h, uniformly in the chosen row polynomial. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Polynomial OddPiPowers

def derivativeWeight : ℕ → ℕ → ℕ
  | 0,0 => 1
  | 0,_+1 => 0
  | j+1,0 => 2 * derivativeWeight j 0
  | j+1,h+1 => 2 * derivativeWeight j (h+1) + derivativeWeight j h

theorem derivativeWeight_zero {j h : ℕ} (hj : j < h) : derivativeWeight j h = 0 := by
  induction j generalizing h with
  | zero => cases h <;> first | omega | rfl
  | succ j ih =>
    obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    rw [derivativeWeight,ih (by omega),ih (by omega)]

theorem entryWithRow_coefficient (v t : ℤ) (j h : ℕ) (f : GaussianInt[X]) :
    (entryWithRow v t j f).coeff h = (derivativeWeight j h : GaussianInt) *
      phase (v*t) * ((v : GaussianInt)*gaussianI)^h *
      ((derivative^[j-h]) f).eval (t : GaussianInt) := by
  have ht : (2 : GaussianInt[X]) = C (2 : GaussianInt) := (map_ofNat C 2).symm
  induction j generalizing h f with
  | zero =>
    have he : entryWithRow v t 0 f = C (phase (v*t) * f.eval (t : GaussianInt)) := by
      simp only [entryWithRow,AddMonoidHom.coe_mk,ZeroHom.coe_mk,rowOperator,eval_map_apply,map_mul]
    rw [he]
    cases h <;> simp [derivativeWeight,coeff_C]
  | succ j ih =>
    rw [entryWithRow_succ,ht,nodeCoefficient,mul_assoc,coeff_add,coeff_C_mul,coeff_C_mul]
    cases h with
    | zero =>
      rw [coeff_X_mul_zero,mul_zero,add_zero,ih]
      simp only [derivativeWeight,pow_zero,mul_one,Nat.sub_zero,Nat.cast_mul,Nat.cast_ofNat,
        Function.iterate_succ_apply]
      ring
    | succ h =>
      rw [coeff_X_mul,ih,ih,derivativeWeight]
      simp only [Nat.succ_sub_succ_eq_sub,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
      by_cases hj : h < j
      · have he : j-h = (j-(h+1))+1 := by omega
        rw [he,Function.iterate_succ_apply]
        ring
      · have he : derivativeWeight j (h+1) = 0 := derivativeWeight_zero (by omega)
        rw [he]
        push_cast
        ring

theorem phase_mod_four (v t : ℤ) : phase (v*t) = phase ((v%4)*t) := by
  unfold phase
  rw [Int.mul_emod v t,Int.mul_emod (v%4) t,Int.emod_emod]

noncomputable def commonEntryCoeff (r t : ℤ) (j h : ℕ) (f : GaussianInt[X]) : GaussianInt :=
  (derivativeWeight j h : GaussianInt) * phase (r*t) * gaussianI^h *
    ((derivative^[j-h]) f).eval (t : GaussianInt)

theorem entryWithRow_coeff_factor (v t : ℤ) (j h : ℕ) (f : GaussianInt[X]) :
    (entryWithRow v t j f).coeff h = (v : GaussianInt)^h * commonEntryCoeff (v%4) t j h f := by
  rw [entryWithRow_coefficient,phase_mod_four,mul_pow,commonEntryCoeff]
  ring

end PiPolynomialValues.FourPeriod
