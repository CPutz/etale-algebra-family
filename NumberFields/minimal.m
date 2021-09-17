Q := Rationals();
Z := Integers();

intrinsic GeneralMinimalPolynomial(K::FldNum) -> RngUPolElt
{}
	R<[c]> := PolynomialRing(Q, Degree(K)-1);
	S<x> := PolynomialRing(R);

	Mrep := &+[c[i] * RepresentationMatrix(K.1^i) : i in [1..Degree(K)-1]];
	M := IdentityMatrix(S,Degree(K)) * x - Mrep;

	return Determinant(M);
end intrinsic;

intrinsic IndexFormMatrix(K::FldNum) -> RngUPolElt
{}
	return IndexFormMatrix(Integers(K));
end intrinsic;

intrinsic IndexFormMatrix(O::RngOrd) -> RngUPolElt
{}
	K := NumberField(O);
	R<[A]> := PolynomialRing(K,Degree(O));
	S := PolynomialRing(Z,Degree(O));
	T<[a]> := PolynomialRing(Z,Degree(O)-1);
	B := Basis(O);
	x := &+[A[i] * B[i] : i in [1..Degree(O)]];

	M := [];
	for j in [0..Degree(O)-1] do
		Cs, Ms := CoefficientsAndMonomials((x - A[1])^j);
		Cs2 := [[R!c*Ms[i] : c in Eltseq(O!Cs[i])] : i in [1..#Cs]];
		row := [Evaluate(&+[Cs2[k,i] : k in [1..#Cs2]],
					[0] cat [a[i] : i in [1..Degree(O)-1]])
					: i in [1..Degree(O)]];
		Append(~M, row);
	end for;

	return MatrixAlgebra(T,Degree(O))!M;
end intrinsic;

intrinsic IndexForm(K::FldNum) -> RngUPolElt
{}
	return Determinant(IndexForm(K));
end intrinsic;

//http://dmat.cfm.cl/dmat/wp-content/uploads/2020/12/TesinaCarlosMunoz.pdf