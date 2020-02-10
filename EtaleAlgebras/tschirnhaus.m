
intrinsic FindTransformation(s::FldElt, t::FldElt) -> RngUPolElt
{Returns the unique polynomial P of degree <= degree(K) such that P(s) = t}
  K := Parent(t);
  n := Degree(K);
  T := BaseField(K);
  M := Matrix(T, n, n, [Eltseq(s^i) : i in [0..n-1]]);
  v := Vector(T, Eltseq(t));

  X := MatrixAlgebra(Rationals(),n);
  Y := VectorSpace(Rationals(),n);
  return PolynomialRing(T)!Eltseq(Solution(X!M, Y!v));

  //PolynomialRing(T)!Eltseq(Solution(M, v));
end intrinsic;