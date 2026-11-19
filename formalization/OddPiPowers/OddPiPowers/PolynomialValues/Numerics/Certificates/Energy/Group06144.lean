module

public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Part06144
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Part07168
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Energy.Part08192

@[expose] public section

namespace PiPolynomialValues.Certificates

def energyGroup06144 : EnergySection 80001 1 6144 3072 := ((energyChunk06144.join (energyChunk06656.join energyChunk07168)).join (energyChunk07680.join (energyChunk08192.join energyChunk08704)))

end PiPolynomialValues.Certificates
