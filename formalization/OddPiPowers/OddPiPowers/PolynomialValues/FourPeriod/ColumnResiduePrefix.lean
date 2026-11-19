module

public import OddPiPowers.PolynomialValues.FourPeriod.Columns

/-! Every signed-band column belongs to one actual progression of step
four in its layer. All its predecessors are again columns of that band. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def columnStart {J : ℕ} {U : Fin J → ℕ} (c : Column U) : ℤ :=
  (c.2.val + (U c.1 : ℤ))%4 - (U c.1 : ℤ)

def columnOrder {J : ℕ} {U : Fin J → ℕ} (c : Column U) : ℕ :=
  (c.2.val + (U c.1 : ℤ)).toNat / 4

def columnClass {J : ℕ} {U : Fin J → ℕ} (c : Column U) := (c.1,columnStart c)

theorem columnStart_bounds {J : ℕ} {U : Fin J → ℕ} (c : Column U) :
    -(U c.1 : ℤ) ≤ columnStart c ∧ columnStart c < -(U c.1 : ℤ)+4 := by
  unfold columnStart
  omega

theorem columnStart_reconstruct {J : ℕ} {U : Fin J → ℕ} (c : Column U) :
    c.2.val = columnStart c + (columnOrder c : ℤ)*4 := by
  obtain ⟨hl,_⟩ := Finset.mem_Icc.mp c.2.property
  unfold columnStart columnOrder
  omega

def columnPredecessor {J : ℕ} {U : Fin J → ℕ} (c : Column U) (k : Fin (columnOrder c+1)) :
    Column U :=
  ⟨c.1, columnStart c + (k.val : ℤ)*4, by
    obtain ⟨hl,_⟩ := columnStart_bounds c
    obtain ⟨_,hu⟩ := Finset.mem_Icc.mp c.2.property
    have he := columnStart_reconstruct c
    have hk := k.isLt
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

theorem columnPredecessor_class {J : ℕ} {U : Fin J → ℕ} (c : Column U) (k : Fin (columnOrder c+1)) :
    columnClass (columnPredecessor c k) = columnClass c := by
  apply Prod.ext
  · rfl
  change (columnStart c + (k.val : ℤ)*4+(U c.1 : ℤ))%4-(U c.1 : ℤ) = columnStart c
  obtain ⟨h₁,h₂⟩ := columnStart_bounds c
  omega

theorem columnPredecessor_order {J : ℕ} {U : Fin J → ℕ} (c : Column U) (k : Fin (columnOrder c+1)) :
    columnOrder (columnPredecessor c k) = k.val := by
  change (columnStart c + (k.val : ℤ)*4+(U c.1 : ℤ)).toNat / 4 = k.val
  obtain ⟨h₁,h₂⟩ := columnStart_bounds c
  omega

theorem columnClass_order_injective {J : ℕ} {U : Fin J → ℕ} :
    Function.Injective (fun c : Column U => (columnClass c,columnOrder c)) := by
  intro a b h
  have hc : columnClass a = columnClass b := congrArg Prod.fst h
  have ho : columnOrder a = columnOrder b := congrArg Prod.snd h
  apply columnLabel_injective U
  apply Prod.ext
  · change a.2.val = b.2.val
    rw [columnStart_reconstruct a,columnStart_reconstruct b,ho,(show columnStart a = columnStart b from congrArg Prod.snd hc)]
  · exact congrArg Fin.val (congrArg Prod.fst hc)

end PiPolynomialValues.FourPeriod
