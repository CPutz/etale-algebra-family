Q := Rationals();

intrinsic GeneralMinimalPolynomial(K::FldNum) -> RngUPolElt
{}
	R<[c]> := PolynomialRing(Q, Degree(K));
	S<x> := PolynomialRing(R);

	Mrep := &+[c[i+1] * RepresentationMatrix(K.1^i) : i in [0..Degree(K)-1]];
	M := IdentityMatrix(S,Degree(K)) * x - Mrep;

	return Determinant(M);
end intrinsic;