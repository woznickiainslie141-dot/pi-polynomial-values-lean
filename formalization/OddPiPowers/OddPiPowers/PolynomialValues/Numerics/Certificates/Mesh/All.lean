module

public import OddPiPowers.PolynomialValues.Numerics.MeshBook
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Block00001
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group00513
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group04609
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group08705
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group12801
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group16897
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group20993
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group25089
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group29185
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group33281
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group37377
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group41473
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group45569
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group49665
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group53761
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group57857
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group61953
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group66049
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group70145
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group74241
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Group78337

@[expose] public section

namespace PiPolynomialValues.Certificates

def primitiveMesh : MeshPiece := ((((mesh00001.piece.append meshGroup00513).append (meshGroup04609.append (meshGroup08705.append meshGroup12801))).append ((meshGroup16897.append meshGroup20993).append (meshGroup25089.append (meshGroup29185.append meshGroup33281)))).append (((meshGroup37377.append meshGroup41473).append (meshGroup45569.append (meshGroup49665.append meshGroup53761))).append ((meshGroup57857.append (meshGroup61953.append meshGroup66049)).append (meshGroup70145.append (meshGroup74241.append meshGroup78337)))))

theorem primitiveMesh_valid : primitiveMesh.Valid :=
  (MeshPiece.append_valid (MeshPiece.append_valid (MeshPiece.append_valid (MeshPiece.append_valid (mesh00001.piece_valid mesh00001_checked) meshGroup00513_valid (by decide +kernel)) (MeshPiece.append_valid meshGroup04609_valid (MeshPiece.append_valid meshGroup08705_valid meshGroup12801_valid (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (MeshPiece.append_valid (MeshPiece.append_valid meshGroup16897_valid meshGroup20993_valid (by decide +kernel)) (MeshPiece.append_valid meshGroup25089_valid (MeshPiece.append_valid meshGroup29185_valid meshGroup33281_valid (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (MeshPiece.append_valid (MeshPiece.append_valid (MeshPiece.append_valid meshGroup37377_valid meshGroup41473_valid (by decide +kernel)) (MeshPiece.append_valid meshGroup45569_valid (MeshPiece.append_valid meshGroup49665_valid meshGroup53761_valid (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (MeshPiece.append_valid (MeshPiece.append_valid meshGroup57857_valid (MeshPiece.append_valid meshGroup61953_valid meshGroup66049_valid (by decide +kernel)) (by decide +kernel)) (MeshPiece.append_valid meshGroup70145_valid (MeshPiece.append_valid meshGroup74241_valid meshGroup78337_valid (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

theorem primitiveMesh_enclosed (i : ℕ) (hi : i≤80000) :
    MeshPrimitiveEnclosed i (primitiveMesh.lookupF i) (primitiveMesh.lookupJ i) :=
  primitiveMesh.lookup_enclosed primitiveMesh_valid (by decide +kernel) (by decide +kernel)
    (by decide +kernel) i (by simpa only [show primitiveMesh.size=80000 by decide +kernel] using hi)

end PiPolynomialValues.Certificates
