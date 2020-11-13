Z := Integers();
Q := Rationals();

intrinsic KleinFormDecomposition(f::RngMPolElt) -> RngMPolElt, RngMPolElt
{Given a Klein form f of degree k, returns polynomials H and G such that
G^2 + 4H^3 is a multiple of f^n where n = 6 - 12/k.}
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

//naive point search over R (finite) of f = 0 for all f in s
function pointsearch(s,R);
	r := Rank(Parent(s[1]));
	return [x : x in CartesianPower(R, r) |
		forall {f : f in s | Evaluate(f, x) eq 0}];
end function;

//returns true if there exists a point x in R^k with x[1] and x[2]
//not both divisible by p which is a solution to f(x) = 0 for all f in s
function existssolutioncoprime(s,R,p);
	r := Rank(Parent(s[1]));
	return exists { x : x in CartesianPower(R, r) |
		(GF(p)!x[1] ne 0 or GF(p)!x[2] ne 0) and
		forall {f : f in s | Evaluate(f, x) eq 0} };
end function;

intrinsic CheckParametrization235(s::SeqEnum, f::RngMPolElt :
	Moduli := Sort(PrimesUpTo(12) cat [4,8,9,27])) -> BoolElt
{Checks }
	//check for local solutions to y^2 = s_12
	_<x> := PolynomialRing(Q);
	s12 := HyperellipticPolynomials(ReducedModel(HyperellipticCurve(Evaluate(s[3],[x,1]))));
	if not HasPointsEverywhereLocally(s12,2) then
		return false;
	end if;

	//check for integral solutions to the system of equations modulo
	//some small Moduli
	H,G := KleinFormDecomposition(f);

	A := 1;
	B := 4;
	C := Z!((A * G^2 + B * H^3) div f^2);

	P<x,y,z,u,v> := AffineSpace(Z,5);
	f1 := z^2 - Evaluate(s[3], [u,v]);
	f2 := (Evaluate(H, [x,y]) - Evaluate(s[2], [u,v]));
	f3 := (Evaluate(G, [x,y]) - Evaluate(s[1], [u,v]));

	//f1 := f1 div Content(f1);
	f2 := f2 div Content(f2);
	f3 := f3 div Content(f3);

	//I := ideal<CoordinateRing(P) | f1,f2,f3>;
	//S := Scheme(P, I);

	failed := false;
	for m in Moduli do
		if IsPrime(m) then
			R := GF(m);
		else
			R := Integers(m);
		end if;

		p := Factorization(m)[1,1];
		if not existssolutioncoprime([f1,f2,f3], R, p) then
			failed := true;
			m;
			break;
		end if;
	end for;

	return not failed;
end intrinsic;

intrinsic QuadraticSearch(C::CrvHyp, D::RngIntElt : Bound := 100) -> SeqEnum
{}
	CD := BaseChange(C, QuadraticField(D));
	J := Jacobian(CD);

	PD := RationalPoints(CD : Bound := Bound);
	PJ := {@ J![p,q] : p,q in PD @};

	P0 := [CD!p : p in RationalPoints(C : Bound := Bound)];
	PJ0 := {@ J![p,q] : p,q in P0 @};

	return SetToSequence(PJ diff PJ0);
end intrinsic;