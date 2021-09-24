Q := Rationals();
Z := Integers();

intrinsic FindObstruction(n::RngIntElt, dZ::RngMPolElt) -> .
{}
	if IsPrime(n) then
		B := GF(n);
	else
		B := Integers(n);
	end if;

	R<x> := PolynomialRing(Z);
	f := x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940;
	K := NumberField(f);

	P  := PolynomialRing(Q, 7);
	P3<[c]> := PolynomialRing(B,9);
	T  := PolynomialRing(P);
	T3<t> := PolynomialRing(P3);
	S  := MatrixAlgebra(T,8);
	S3 := MatrixAlgebra(T3,8);

	g := t^8 + 16*c[9]*t^7 + 600000*c[8]^5*c[9] + 140*c[9]^2*t^6 + 
 		1120*c[9]^3*t^5 + 3990*c[9]^4*t^4 + 7056*c[9]^5*t^3 + 
 		6636*c[9]^6*t^2 + (-400000*c[8]^5 + 3200*c[9]^7)*t +
 		625*c[9]^8;

	phi1 := hom<P -> P3 | [P3.i : i in [1..7]]>;
	phi2 := hom<T -> T3 | phi1, T3.1>;
	phi3 := hom<S -> S3 | phi2>;

	//Q3<[d]> := quo<P3 | [c[i]^3 - c[i] : i in [1..9]]>;
	//Q3<[d]> := quo<P3 | [c[i]^8 - c[i]^2 : i in [1..9]]>;
	//Q3<[d]> := quo<P3 | [c[i]^21 - c[i]^3 : i in [1..9]]>;
	//phi4 := hom<P3 -> Q3 | [d[i] : i in [1..9]]>;

	X := MatrixAlgebra(P,8);
	X3 := MatrixAlgebra(P3,8);
	//XQ := MatrixAlgebra(Q3,8);
	psi1 := hom<X -> X3 | phi1>;
	//psi2 := hom<X3 -> XQ | phi4>;

	M := GeneralMinimalPolynomialMatrix(K);
	I := IndexFormMatrix(K);

	//cs := [P3!phi4(c) : c in Coefficients(g - Determinant(phi3(M)))];
	//d := P3!Determinant(psi2(psi1(I))) - 1;
	cs := Coefficients(g - Determinant(phi3(M)));
	//d := Determinant(psi1(I)) - 1;
	d := phi1(dZ);

	return cs cat [d];
end intrinsic;

intrinsic FindObstructionZ() -> .
{}
	R<x> := PolynomialRing(Z);
	f := x^8 + 4*x^7 - 28*x^6 - 168*x^5 - 140*x^4 + 560*x^3 + 840*x^2 - 480*x - 940;
	K := NumberField(f);

	P7 := PolynomialRing(Q,7);
	P<[c]>  := PolynomialRing(Q, 9);
	T<t>  := PolynomialRing(P);

	g := t^8 + 16*c[9]*t^7 + 600000*c[8]^5*c[9] + 140*c[9]^2*t^6 + 
 		1120*c[9]^3*t^5 + 3990*c[9]^4*t^4 + 7056*c[9]^5*t^3 + 
 		6636*c[9]^6*t^2 + (-400000*c[8]^5 + 3200*c[9]^7)*t +
 		625*c[9]^8;

 	phi1 := hom<P7 -> P | [P.i : i in [1..7]]>;
 	phi2 := hom<PolynomialRing(P7) -> T | phi1, t>;

	M := GeneralMinimalPolynomialMatrix(K);
	cs := Coefficients(g - phi2(Determinant(M)));

	return cs;
end intrinsic;