module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group00000
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group03072
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group06144
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group09216
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group12288
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group15360
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group18432
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group21504
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group24576
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group27648
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group30720
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group33792
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group36864
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group39936
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group43008
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group46080
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group49152
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group52224
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group55296
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group58368
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group61440
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group64512
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group67584
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group70656
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group73728
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group76800
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Group79872

@[expose] public section

namespace PiPolynomialValues.Certificates

def fineEnergyBasis : EnergySection 80001 1 0 80001 := ((((energyGroup00000.join (energyGroup03072.join energyGroup06144)).join (energyGroup09216.join (energyGroup12288.join energyGroup15360))).join ((energyGroup18432.join (energyGroup21504.join energyGroup24576)).join ((energyGroup27648.join energyGroup30720).join (energyGroup33792.join energyGroup36864)))).join (((energyGroup39936.join (energyGroup43008.join energyGroup46080)).join ((energyGroup49152.join energyGroup52224).join (energyGroup55296.join energyGroup58368))).join ((energyGroup61440.join (energyGroup64512.join energyGroup67584)).join ((energyGroup70656.join energyGroup73728).join (energyGroup76800.join energyGroup79872)))))

end PiPolynomialValues.Certificates
