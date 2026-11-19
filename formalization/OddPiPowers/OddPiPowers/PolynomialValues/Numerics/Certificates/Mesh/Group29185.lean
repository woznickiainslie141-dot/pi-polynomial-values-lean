module

public import OddPiPowers.PolynomialValues.Numerics.MeshBook
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Part29185
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Part30209
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Part31233
public import OddPiPowers.PolynomialValues.Numerics.Certificates.Mesh.Part32257

@[expose] public section

namespace PiPolynomialValues.Certificates

def meshGroup29185 : MeshPiece := (((mesh29185.piece.append mesh29697.piece).append (mesh30209.piece.append mesh30721.piece)).append ((mesh31233.piece.append mesh31745.piece).append (mesh32257.piece.append mesh32769.piece)))

theorem meshGroup29185_valid : meshGroup29185.Valid :=
  (MeshPiece.append_valid (MeshPiece.append_valid (MeshPiece.append_valid (mesh29185.piece_valid mesh29185_checked) (mesh29697.piece_valid mesh29697_checked) (by decide +kernel)) (MeshPiece.append_valid (mesh30209.piece_valid mesh30209_checked) (mesh30721.piece_valid mesh30721_checked) (by decide +kernel)) (by decide +kernel)) (MeshPiece.append_valid (MeshPiece.append_valid (mesh31233.piece_valid mesh31233_checked) (mesh31745.piece_valid mesh31745_checked) (by decide +kernel)) (MeshPiece.append_valid (mesh32257.piece_valid mesh32257_checked) (mesh32769.piece_valid mesh32769_checked) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end PiPolynomialValues.Certificates
