Q := Rationals();
Z := Integers();

intrinsic HenselLift(fs::SeqEnum[RngMPolElt], x::SeqEnum[FldFinElt], m::RngIntElt) -> .
{}
	p := Characteristic(Parent(x[1]));
	RZ := RSpace(Z,7);
	Rp := RSpace(GF(p),7);
	Mp := MatrixAlgebra(GF(p),7);

	fs := RSpace(Parent(fs[1]), #fs)!fs;

	Jx := Mp!Evaluate(JacobianMatrix(Eltseq(fs)), x);
	b,Jxi := IsInvertible(Jx);
	//assert b: "Jacobian matrix at p must be invertible";
	assert b;

	Jxi := Transpose(Jxi);
	
	for k := 2 to m do
		Zpe := Integers(p^k);
		Rpe := RSpace(Zpe, 7);
		y := RZ!(Rp!-RSpace(Parent(x[1]),7)!(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1)) * Jxi);
		x := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!y);
	end for;

	return x;
end intrinsic;

intrinsic Script257(p::RngIntElt, m::RngIntElt) -> .
{}
	R<a,b,c,d,e,f,g> := PolynomialRing(Z,7);
	_<y> := PolynomialRing(R);

	F := a * (y^2 + b*y + c)^3 * (y - 1);
	G := y;
	H := a * (y^3 + d*y^2 + e*y + f)^2 * (y - g);

	fs := Coefficients(F - G - H);
	
	A := AffineSpace(GF(p),7);
	S := Scheme(A, fs);

	Ps := RationalPoints(S);

	return fs,HenselLift(fs, Eltseq(Ps[1]), m);
end intrinsic;