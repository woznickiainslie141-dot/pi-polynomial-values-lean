module

public import OddPiPowers.PolynomialValues.Numerics.SelectedRowFloors
public import OddPiPowers.PolynomialValues.Numerics.FactorialCostData

/-! Identify the residue-ordered rows of the selected determinant with the
increasing signed node indices used by every reference field and center. -/

@[expose] public section

namespace PiPolynomialValues.FourPeriod

def signedNode (s : Shape) (i : Fin s.rows.length) : ℤ := (i.val : ℤ)-(s.ratios.length-1 : ℕ)
def rankOfNode (s : Shape) (v : ℤ) : ℕ := (v+(s.ratios.length-1 : ℕ)).toNat

def scanForward (s : Shape) (g : List (List ℤ)) (h : 0 < s.rows.length) (i : Fin g.flatten.length) : Fin s.rows.length :=
  ⟨rankOfNode s (scannedNode g i)%s.rows.length,Nat.mod_lt _ h⟩

def scanBack (s : Shape) (g : List (List ℤ)) (h : 0 < g.flatten.length) (i : Fin s.rows.length) : Fin g.flatten.length :=
  ⟨g.flatten.idxOf (signedNode s i)%g.flatten.length,Nat.mod_lt _ h⟩

structure ScanOrder (s : Shape) (g : List (List ℤ)) where
  rank : Fin g.flatten.length ≃ Fin s.rows.length
  node : ∀ i, scannedNode g i=signedNode s (rank i)
  ratio : ∀ i, s.ratioAt (scannedNode g i)=s.rows.get (rank i)

def scanOrderOfTests (s : Shape) (g : List (List ℤ)) (h : 0 < s.rows.length) (hg : 0 < g.flatten.length)
    (hl : ∀ i, scanBack s g hg (scanForward s g h i)=i)
    (hr : ∀ i, scanForward s g h (scanBack s g hg i)=i)
    (hn : ∀ i, scannedNode g i=signedNode s (scanForward s g h i))
    (ha : ∀ i, s.ratioAt (scannedNode g i)=s.rows.get (scanForward s g h i)) : ScanOrder s g :=
  ⟨⟨scanForward s g h,scanBack s g hg,hl,hr⟩,hn,ha⟩

def quadraticScanOrder : ScanOrder quadraticShape quadraticNodeGroups :=
  scanOrderOfTests _ _ (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def cubicScanOrder : ScanOrder cubicShape cubicNodeGroups :=
  scanOrderOfTests _ _ (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ScanOrder.mass_at {s : Shape} {g : List (List ℤ)} (S : ScanOrder s g) (i : Fin g.flatten.length) :
    s.massList[(S.rank i).val]?.getD 0=s.rowMassQ (s.ratioAt (scannedNode g i)) := by
  rw [S.ratio]
  simp [Shape.massList,List.getElem?_eq_getElem (l := s.rows) (S.rank i).isLt]

end PiPolynomialValues.FourPeriod
