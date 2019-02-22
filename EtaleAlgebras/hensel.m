Z := Integers();

intrinsic HenselLift(f::SeqEnum[RngMPolElt], x::ModTupRngElt, m::RngIntElt) -> SeqEnum
{Lifts a solution x of f modulo m = p^k to all possible solutions of f modulo p^2k}
	P := Parent(f[1]);
	Pp := PolynomialRing(Integers(m), Rank(P));
	PZ := PolynomialRing(Z, Rank(P));
	require Rank(P) eq #f: "System of equations must be zero dimensional";

	//substitution
	g := Evaluate(f, [ Z!x[i] + m * P.i : i in [1..Rank(P)] ]);
	g := [Pp!(PZ!gi div m) : gi in g];

	J := Transpose(JacobianMatrix(g));
	zero := [0 : i in [1..#g]];
	J0 := Evaluate(J, zero);
	S  := RSpace(Integers(m), Rank(P));
	S2 := RSpace(Integers(m^2), Rank(P));
	SZ := RSpace(Z, Rank(P));
	g0 := -S!Evaluate(g, zero);
	sol, v, N := IsConsistent(J0, g0);
	if sol then
		y := SZ!x + m*SZ!v;
		return [S2!(y + m*SZ!n) : n in N];
	else
		return [];
	end if;
end intrinsic;

intrinsic HenselLiftSingle(f::SeqEnum[RngMPolElt], x::ModTupRngElt, p::RngIntElt, M::RngIntElt) -> BoolElt, .
{Lifts a solution x of f modulo p to a single solution of f modulo M (where M is a power of p)}
	return HenselLiftSingle2(f, x, p, M);
end intrinsic;


intrinsic HenselLiftSingle2(f::SeqEnum[RngMPolElt], x::ModTupRngElt, m::RngIntElt, M::RngIntElt) -> BoolElt, .
{Lifts a solution x of f modulo m = p^k to a single solution of f modulo p^2k}
	P := Parent(f[1]);
	Pp := PolynomialRing(Integers(m), Rank(P));
	PZ := PolynomialRing(Z, Rank(P));
	require Rank(P) eq #f: "System of equations must be zero dimensional";

	//substitution
	g := Evaluate(f, [ Z!x[i] + m * P.i : i in [1..Rank(P)] ]);
	g := [Pp!(PZ!gi div m) : gi in g];

	J := Transpose(JacobianMatrix(g));
	zero := [0 : i in [1..#g]];
	J0 := Evaluate(J, zero);
	S  := RSpace(Integers(m), Rank(P));
	S2 := RSpace(Integers(m^2), Rank(P));
	SZ := RSpace(Z, Rank(P));
	g0 := -S!Evaluate(g, zero);
	sol, v, N := IsConsistent(J0, g0);
	if sol then
		y := SZ!x + m*SZ!v;
		if m^2 ge M then
			return true, S2!y;
		else
			for n in N do
				b, x := HenselLiftSingle2(f, S2!(y + m*SZ!n), m^2, M);
				if b then
					return true, x;
				end if;
			end for;
			return false, 0;
		end if;
	else
		return false, 0;
	end if;
end intrinsic;

intrinsic HenselLiftable(f::SeqEnum[RngMPolElt], x::SeqEnum, p::RngIntElt) -> BoolElt
{Returns whether one can lift the solution x of f(x) = 0 mod p to a solution in Zp}
	P := Parent(f[1]);
	require Rank(P) eq #f: "System of equations must be zero dimensional";

	J := JacobianMatrix(f);
	D := Determinant(Evaluate(J, Eltseq(x)));
	vJ := Valuation(D, p);
	vf := [Valuation(c, p) : c in Evaluate(f, x)];
	return forall {v : v in vf | v gt 2*vJ};
end intrinsic;

intrinsic Lifts(x::ModTupRngElt, p::RngIntElt) -> SeqEnum[ModTupRngElt]
{Lifts a point in (Z/mZ)^k to a point list of points in (Z/mpZ)^k}
	V := Parent(x);
	R := BaseRing(V);
	m := #R;
	S  := RSpace(Integers(m * p), Rank(V));
	Sp := RSpace(Integers(p), Rank(V));
	SZ := RSpace(Z, Rank(V));
	return [S!SZ!x + S!(m*SZ!y) : y in Sp];
end intrinsic;

intrinsic Evaluate(f::SeqEnum[RngMPolElt], x::SeqEnum) -> SeqEnum
{Evaluates a sequence of polynomials f at a point x}
	return [Evaluate(fi, x) : fi in f];
end intrinsic;

intrinsic Roots(f::RngMPolElt) -> SeqEnum
{A list of all roots of f over its base ring}
	P := Parent(f);
	R := BaseRing(P);
	S := RSpace(R, Rank(P));
	return [x : x in S | Evaluate(f, Eltseq(x)) eq 0];
end intrinsic;

intrinsic Roots(f::SeqEnum[RngMPolElt]) -> SeqEnum
{A list of all simultanious roots of the fi over their base ring}
	P := Parent(f[1]);
	R := BaseRing(P);
	S := RSpace(R, Rank(P));
	return SetToSequence(&meet [{@ x : x in S | Evaluate(fi, Eltseq(x)) eq 0 @} : fi in f]);
end intrinsic;

intrinsic Homogenization(f::RngMPolElt) -> RngMPolElt
{Homogenizes f}
	R := Parent(f);
	S := PolynomialRing(BaseRing(R), Rank(R)+1);
	Rt<t> := PolynomialRing(S);
	g := Evaluate(f, [t * S.i : i in [1..Rank(R)]]);
	return Evaluate(ReciprocalScale(g, S.(Rank(R)+1)), 1);
end intrinsic;

intrinsic Testje() -> SeqEnum
{}
	Rc<[c]> := PolynomialRing(Z, 7);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c[1]+c[2]*x+c[3]*x^2+c[4]*x^3+c[5]*x^4+c[6]*x^5+c[7]*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	return Coefficients(15*r - (phi + (1) * 2^5));
end intrinsic;

intrinsic Testje2() -> SeqEnum
{}
	R<a> := PolynomialRing(Z);
	Rc<[c]> := PolynomialRing(R, 7);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c[1]+c[2]*x+c[3]*x^2+c[4]*x^3+c[5]*x^4+c[6]*x^5+c[7]*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	return Coefficients(15*r - (phi + (1 + 2*a)));
end intrinsic;

intrinsic ChangeRing(f::SeqEnum[RngMPolElt], R::Rng) -> SeqEnum[RngMPolElt]
{}
	S := ChangeRing(Parent(f[1]),R);
	return [S!fi : fi in f];
end intrinsic;