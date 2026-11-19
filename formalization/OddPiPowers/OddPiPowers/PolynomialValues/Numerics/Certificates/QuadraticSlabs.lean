module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs01
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs02
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs03
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs04
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs05
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs06
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs07
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs08
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs09
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs10
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs11
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs12
public import OddPiPowers.PolynomialValues.Numerics.Certificates.QuadraticSlabs13

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

def quadraticSlabs : List Slab :=
  quadraticSlabs01 ++
  quadraticSlabs02 ++
  quadraticSlabs03 ++
  quadraticSlabs04 ++
  quadraticSlabs05 ++
  quadraticSlabs06 ++
  quadraticSlabs07 ++
  quadraticSlabs08 ++
  quadraticSlabs09 ++
  quadraticSlabs10 ++
  quadraticSlabs11 ++
  quadraticSlabs12 ++
  quadraticSlabs13

theorem quadraticSlabs_checked :
    CheckedSlabs quadraticShape ⟨5, 1⟩ ⟨5778404, 71447⟩ quadraticSlabs 241 117144683794708 :=
  quadraticSlabs01_checked.append (quadraticSlabs02_checked.append (quadraticSlabs03_checked.append (quadraticSlabs04_checked.append (quadraticSlabs05_checked.append (quadraticSlabs06_checked.append (quadraticSlabs07_checked.append (quadraticSlabs08_checked.append (quadraticSlabs09_checked.append (quadraticSlabs10_checked.append (quadraticSlabs11_checked.append (quadraticSlabs12_checked.append (quadraticSlabs13_checked))))))))))))

end PiPolynomialValues.PrimeWindow
