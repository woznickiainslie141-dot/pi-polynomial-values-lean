module

public import OddPiPowers.PolynomialValues.Analysis.BandCharge
public import OddPiPowers.PolynomialValues.Analysis.AllocationEnergy

/-! Reflect all columns on one face. The derivative layer and the complete
empirical frequency charge are preserved by a single permutation. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

open Finset

def reflectColumn {n : ℕ} {U : Fin n → ℕ} (c : Column U) : Column U :=
  ⟨c.1,-c.2.val,by
    obtain ⟨hl,hu⟩ := mem_Icc.mp c.2.property
    exact mem_Icc.mpr ⟨by omega,by omega⟩⟩

def columnReflection {n : ℕ} (U : Fin n → ℕ) (face : Bool) : Column U ≃ Column U :=
  match face with
  | false => Equiv.refl _
  | true => ⟨reflectColumn,reflectColumn,fun ⟨j,x⟩ => by simp [reflectColumn],
        fun ⟨j,x⟩ => by simp [reflectColumn]⟩

theorem columnReflection_layer {n : ℕ} (U : Fin n → ℕ) (face : Bool) (c : Column U) :
    (columnReflection U face c).1=c.1 := by cases face <;> rfl

theorem columnReflection_frequency {n : ℕ} (U : Fin n → ℕ) (face : Bool) (c : Column U) :
    (columnReflection U face c).2.val=(if face then -c.2.val else c.2.val) := by cases face <;> rfl

theorem bandFrequency_value (s : Shape) (hw : ∀ w∈s.widths, w≤10000) {t : ℕ}
    (hN : 0 < s.massUnit*t) (c : Column (s.band t)) :
    (bandFrequency s t c : ℝ)=(c.2.val : ℝ)*((s.massUnit*t : ℕ) : ℝ)⁻¹ := by
  have hW : s.band t c.1≤s.massUnit*t :=
    Nat.mul_le_mul_right t (Nat.mul_le_mul_right s.rows.sum (hw _ (List.get_mem _ _)))
  have hh := mem_Icc.mp c.2.property
  have hLo : -((s.massUnit*t : ℕ) : ℝ)≤(c.2.val : ℝ) := by exact_mod_cast (show -((s.massUnit*t : ℕ) : ℤ)≤c.2.val by omega)
  have hHi : (c.2.val : ℝ)≤((s.massUnit*t : ℕ) : ℝ) := by exact_mod_cast (show c.2.val≤((s.massUnit*t : ℕ) : ℤ) by omega)
  have hp : 0 < ((s.massUnit*t : ℕ) : ℝ) := by exact_mod_cast hN
  apply projected_frequency (le_refl (-1 : ℝ)) (le_refl (1 : ℝ))
  rw [← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ hp).mpr (by simpa using hLo),(div_le_iff₀ hp).mpr (by simpa using hHi)⟩

theorem allocatedBandCharge {s : Shape} {t n V : ℕ} (m : Fin V → ℕ)
    (d : ((v : Fin V) × Fin (m v)) ≃ Fin n) (e : Fin n ≃ Column (s.band t)) (face : Bool) :
    (∑ v, allocationCharge m d (fun i => bandFrequency s t (columnReflection _ face (e i)))
      ((s.massUnit*t : ℕ) : ℝ) v)=bandCharge s t :=
  allocatedCharge_sum (d.trans (e.trans (columnReflection _ face)))

end PiPolynomialValues.FourPeriod
