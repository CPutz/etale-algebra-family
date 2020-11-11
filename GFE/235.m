Z := Integers();
Q := Rationals();

intrinsic DecomposeKleinForm(f::RngMPolElt) -> RngMPolElt, RngMPolElt
{}
	require IsHomogeneous(f) : "Argument 1 must be homogeneous";
	R := Parent(f);
	k := Degree(f);

	H := Determinant(Matrix([
		[Derivative(Derivative(f,R.1),R.1), Derivative(Derivative(f,R.1),R.2)],
		[Derivative(Derivative(f,R.2),R.1), Derivative(Derivative(f,R.2),R.2)]]))
		div ((k-1)^2);
	G := Determinant(Matrix([
		[Derivative(f, R.1), Derivative(f, R.2)],
		[Derivative(H, R.1), Derivative(H, R.2)]]))
		div (k-2);
	return H,G;
end intrinsic;

intrinsic CheckParametrization(s::SeqEnum, f::RngMPolElt) -> BoolElt
{}
	H,G := DecomposeKleinForm(f);

	A := 1;
	B := 4;
	C := Z!((A * G^2 + B * H^3) div f^2);

	P<x,y,z,u,v> := AffineSpace(Z,5);
	f1 := z^2 - Evaluate(s[3], [u,v]);
	f2 := (Evaluate(H, [x,y]) - Evaluate(s[2], [u,v]));
	f3 := (Evaluate(G, [x,y]) - Evaluate(s[1], [u,v]));

	f1 := f1 div Content(f1);
	f2 := f2 div Content(f2);
	f3 := f3 div Content(f3);

	I := ideal<CoordinateRing(P) | f1,f2,f3>;
	S := Scheme(P, I);

	failed := false;
	for p in PrimesUpTo(12) do
		if p eq 2 then
			R := Integers(8);
		elif p eq 3 then
			R := Integers(9);
		else
			R := GF(p);
		end if;

		points := [p : x,y,z,u,v in R |
			Evaluate(f1,p) eq 0 and
			Evaluate(f2,p) eq 0 and
			Evaluate(f3,p) eq 0
			where p := <x,y,z,u,v>];

		//points := RationalPoints(BaseChange(S, GF(p)));
		// x and y are coprime
		if #[s : s in points | Z!s[1] mod p ne 0 or Z!s[2] mod p ne 0] eq 0 then
			failed := true;
		p;
			break;
		end if;
	end for;

	return not failed;
end intrinsic;
