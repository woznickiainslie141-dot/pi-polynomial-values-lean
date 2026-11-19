module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs01
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs02
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs03
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs04
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs05
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs06
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs07
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs08
public import OddPiPowers.PolynomialValues.Numerics.Certificates.CubicSlabs09

@[expose] public section

namespace PiPolynomialValues.PrimeWindow

open FourPeriod

def cubicSlabs : List Slab :=
  cubicSlabs01 ++
  cubicSlabs02 ++
  cubicSlabs03 ++
  cubicSlabs04 ++
  cubicSlabs05 ++
  cubicSlabs06 ++
  cubicSlabs07 ++
  cubicSlabs08 ++
  cubicSlabs09

theorem cubicSlabs_checked :
    CheckedSlabs cubicShape ⟨8, 1⟩ ⟨39000, 451⟩ cubicSlabs 161 2867530575302 :=
  cubicSlabs01_checked.append (cubicSlabs02_checked.append (cubicSlabs03_checked.append (cubicSlabs04_checked.append (cubicSlabs05_checked.append (cubicSlabs06_checked.append (cubicSlabs07_checked.append (cubicSlabs08_checked.append (cubicSlabs09_checked))))))))

end PiPolynomialValues.PrimeWindow
