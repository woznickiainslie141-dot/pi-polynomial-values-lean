module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs01
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs02
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs03
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs04
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs05
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs06
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs07
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs08
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs09
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs10
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs11
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs12
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs13
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs14
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs15
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs16
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs17
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticArcs18

@[expose] public section

namespace PiPolynomialValues

def quadraticArcs : List ArcRow :=
  quadraticArcs01 ++
  quadraticArcs02 ++
  quadraticArcs03 ++
  quadraticArcs04 ++
  quadraticArcs05 ++
  quadraticArcs06 ++
  quadraticArcs07 ++
  quadraticArcs08 ++
  quadraticArcs09 ++
  quadraticArcs10 ++
  quadraticArcs11 ++
  quadraticArcs12 ++
  quadraticArcs13 ++
  quadraticArcs14 ++
  quadraticArcs15 ++
  quadraticArcs16 ++
  quadraticArcs17 ++
  quadraticArcs18

theorem quadraticArcs_chain : arcChain 0 1 quadraticArcs = true ∧ quadraticArcs.length = 107 := by
  decide +kernel

theorem quadraticArcs_checked : quadraticArcs.all (fun e => e.passes (41059/250000)) = true := by
  simp only [quadraticArcs, List.all_append, quadraticArcs01_checked,
    quadraticArcs02_checked,
    quadraticArcs03_checked,
    quadraticArcs04_checked,
    quadraticArcs05_checked,
    quadraticArcs06_checked,
    quadraticArcs07_checked,
    quadraticArcs08_checked,
    quadraticArcs09_checked,
    quadraticArcs10_checked,
    quadraticArcs11_checked,
    quadraticArcs12_checked,
    quadraticArcs13_checked,
    quadraticArcs14_checked,
    quadraticArcs15_checked,
    quadraticArcs16_checked,
    quadraticArcs17_checked,
    quadraticArcs18_checked, Bool.true_and]

theorem quadraticArcs_integrals (e : ArcRow) (h : e ∈ quadraticArcs) : e.enclosed (41059/250000) :=
  ArcRow.enclosed_of_passes _ e (List.all_eq_true.mp quadraticArcs_checked _ h)

end PiPolynomialValues
