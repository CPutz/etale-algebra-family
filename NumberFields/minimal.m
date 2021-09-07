Q := Rationals();
Z := Integers();

intrinsic GeneralMinimalPolynomial(K::FldNum) -> RngUPolElt
{}
	R<[c]> := PolynomialRing(Q, Degree(K));
	S<x> := PolynomialRing(R);

	Mrep := &+[c[i+1] * RepresentationMatrix(K.1^i) : i in [0..Degree(K)-1]];
	M := IdentityMatrix(S,Degree(K)) * x - Mrep;

	return Determinant(M);
end intrinsic;

intrinsic MonogenicityPolynomial(K::FldNum) -> RngUPolElt
{}
	R<[A]> := PolynomialRing(K,Degree(K));
	S := PolynomialRing(Z,Degree(K));
	OK := Integers(K);
	B := IntegralBasis(K);
	x := &+[A[i] * B[i] : i in [1..Degree(K)]];

	M := [];
	for j in [1..Degree(K)] do
		Cs, Ms := CoefficientsAndMonomials((x - A[1])^j);
		Cs2 := [[R!c*Ms[i] : c in Eltseq(OK!Cs[i])] : i in [1..#Cs]];
		row := [&+[Cs2[k,i] : k in [1..#Cs2]] : i in [1..Degree(K)]];
		Append(~M, row);
	end for;

	return Determinant(MatrixAlgebra(S,Degree(K))!M);
end intrinsic;

//http://dmat.cfm.cl/dmat/wp-content/uploads/2020/12/TesinaCarlosMunoz.pdf