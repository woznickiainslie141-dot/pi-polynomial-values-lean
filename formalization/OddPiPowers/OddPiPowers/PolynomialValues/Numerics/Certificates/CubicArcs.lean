module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs01
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs02
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs03
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs04
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs05
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs06
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs07
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs08
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs09
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs10
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs11
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs12
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs13
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs14
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs15
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs16
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicArcs17

@[expose] public section

namespace PiPolynomialValues

def cubicArcs : List ArcRow :=
  cubicArcs01 ++
  cubicArcs02 ++
  cubicArcs03 ++
  cubicArcs04 ++
  cubicArcs05 ++
  cubicArcs06 ++
  cubicArcs07 ++
  cubicArcs08 ++
  cubicArcs09 ++
  cubicArcs10 ++
  cubicArcs11 ++
  cubicArcs12 ++
  cubicArcs13 ++
  cubicArcs14 ++
  cubicArcs15 ++
  cubicArcs16 ++
  cubicArcs17

theorem cubicArcs_chain : arcChain 0 1 cubicArcs = true ∧ cubicArcs.length = 98 := by
  decide +kernel

theorem cubicArcs_checked : cubicArcs.all (fun e => e.passes (1289/8000)) = true := by
  simp only [cubicArcs, List.all_append, cubicArcs01_checked,
    cubicArcs02_checked,
    cubicArcs03_checked,
    cubicArcs04_checked,
    cubicArcs05_checked,
    cubicArcs06_checked,
    cubicArcs07_checked,
    cubicArcs08_checked,
    cubicArcs09_checked,
    cubicArcs10_checked,
    cubicArcs11_checked,
    cubicArcs12_checked,
    cubicArcs13_checked,
    cubicArcs14_checked,
    cubicArcs15_checked,
    cubicArcs16_checked,
    cubicArcs17_checked, Bool.true_and]

theorem cubicArcs_integrals (e : ArcRow) (h : e ∈ cubicArcs) : e.enclosed (1289/8000) :=
  ArcRow.enclosed_of_passes _ e (List.all_eq_true.mp cubicArcs_checked _ h)

end PiPolynomialValues
