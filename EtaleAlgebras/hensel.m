Z := Integers();
Q := Rationals();

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

intrinsic HenselLiftSingle(f::SeqEnum[RngMPolElt], x::ModTupRngElt, m::RngIntElt, M::RngIntElt) -> BoolElt, .
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
		y; v; N;
		if m^2 ge M then
			return true, S2!y;
		else
			for n in N do
				b, x := HenselLiftSingle(f, S2!(y + m*SZ!n), m^2, M);
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

intrinsic Hensel(x::Pt, prec::RngIntElt:
	prec0:=Min([AbsolutePrecision(xi) : xi in Eltseq(x)])) -> BoolElt, .
{Lifts an approximate point x over Qp on a 0-dimensional affine scheme over
the rationals to precision prec}
	S := Parent(x);
	K := Ring(S);
	p := UniformizingElement(K);
	X := Scheme(S);
	J := Transpose(JacobianMatrix(X));

	p0 := p^prec0;
	x2 := [ChangePrecision(xi, prec0 + Precision(xi)) : xi in Eltseq(x)];

	d := Dimension(AmbientSpace(X));
	Sp := RSpace(Integers(Z!p0), d);
	Mp := MatrixAlgebra(Integers(Z!p0), d);
	SZ := RSpace(Z, d);
	MZ := MatrixAlgebra(Z, d);
	SK := RSpace(K, d);

	Jx := Mp!MZ!(Evaluate(J, Eltseq(x)));
	fx := Sp!(SZ!Evaluate(DefiningPolynomials(X),x2) div p0);
	sol, v, N := IsConsistent(Jx, -fx);

	if sol then
		y := SK!x2 + SK!(p0*SZ!v);
		if 2*prec0 ge prec then
			return true, X(K)!Eltseq(y);
		else
			for n in N do
				b, z := Hensel(X(K)!Eltseq(y + p0*SZ!n), prec: prec0:=2*prec0);
				if b then
					return true, z;
				end if;
			end for;
			return  false, 0;
		end if;
	else 
		return false, 0;
	end if;
end intrinsic;

intrinsic HenselLiftSingle3(f::SeqEnum[RngMPolElt], x::ModTupRngElt, p::RngIntElt, m::RngIntElt, M::RngIntElt) -> BoolElt, .
{Lifts a solution x of f modulo m = p^k to a single solution of f modulo p^2k}
	m;
	pm := p^m;
	P := Parent(f[1]);
	Pp := PolynomialRing(GF(p), Rank(P));
	PZ := PolynomialRing(Z, Rank(P));
	require Rank(P) eq #f: "System of equations must be zero dimensional";

	//substitution
	g := Evaluate(f, [ Z!x[i] + pm * P.i : i in [1..Rank(P)] ]);
	g := [Pp!(PZ!gi div pm) : gi in g];
	J := Transpose(JacobianMatrix(g));
	zero := [0 : i in [1..#g]];
	J0 := Evaluate(J, zero);
	Sp := KSpace(GF(p), Rank(P));
	S  := RSpace(Integers(pm * p), Rank(P));
	SZ := RSpace(Z, Rank(P));
	g0 := -Sp!Evaluate(g, zero);
	sol, v, N := IsConsistent(J0, g0);
	if sol then
		y := SZ!x + pm*SZ!v;
		if m ge M then
			return true, S!y;
		else
			for n in N do
				b, x := HenselLiftSingle3(f, S!(y + pm*SZ!n), p, m+1, M);
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

intrinsic HenselLiftable(f::SeqEnum[RngMPolElt], x::ModTupRngElt, p::RngIntElt) -> BoolElt
{Returns whether one can lift the solution x of f(x) = 0 mod p to a solution in Zp}
	P := Parent(f[1]);
	require Rank(P) eq #f: "System of equations must be zero dimensional";
	SZ := RSpace(Z, Rank(P));

	J := JacobianMatrix(f);
	D := Determinant(Evaluate(J, Eltseq(SZ!x)));
	vJ := Valuation(D, p);
	vf := [Valuation(c, p) : c in Evaluate(f, Eltseq(SZ!x))];
	vJ; vf;
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

intrinsic RootsFamily(f::SeqEnum[RngMPolElt]) -> .
{A list of all simultanious roots of the fi over their base ring}
	Rc := Parent(f[1]);
	P := BaseRing(Rc);
	R := BaseRing(P);
	Lin := [P ! Eltseq(x) : x in RSpace(R, 2)];
	S := CartesianProduct([Lin : i in [1..Rank(Rc)]]);
	return [x : x in S | forall { fi : fi in f | Evaluate(fi, TupSeq(x)) eq 0 }];
end intrinsic;

intrinsic Homogenization(f::RngMPolElt) -> RngMPolElt
{Homogenizes f}
	R := Parent(f);
	S := PolynomialRing(BaseRing(R), Rank(R)+1);
	Rt<t> := PolynomialRing(S);
	g := Evaluate(f, [t * S.i : i in [1..Rank(R)]]);
	return Evaluate(ReciprocalScale(g, S.(Rank(R)+1)), 1);
end intrinsic;

intrinsic ChangeRing(f::SeqEnum[RngMPolElt], R::Rng) -> SeqEnum[RngMPolElt]
{}
	S := ChangeRing(Parent(f[1]),R);
	return [S!fi : fi in f];
end intrinsic;

intrinsic Testje(a::RngElt) -> SeqEnum
{}
	Rc<[c]> := PolynomialRing(Parent(a), 7);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c[1]+c[2]*x+c[3]*x^2+c[4]*x^3+c[5]*x^4+c[6]*x^5+c[7]*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	return Coefficients(15*r - (phi + a));
end intrinsic;

intrinsic Testje2a() -> SeqEnum
{}
	Rc<a,c1,c2,c3,c4,c5,c6,c7> := PolynomialRing(Q, 8);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	return Coefficients(15*r - (phi + 2^5*a));
end intrinsic;

intrinsic Testje2(a::RngElt) -> SeqEnum
{}
	Rc<[c]> := PolynomialRing(Parent(a), 2);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x^2+x+1),
		t - (c[1]+c[2]*x));
	phi := t^2 + t + 1;
	return Coefficients(r - (phi + 2*a * t));
end intrinsic;

intrinsic Testje3() -> SeqEnum
{}
	Rc<c1,c2,c3,c4,c5,c6,c7,a,e> := PolynomialRing(Q, 9);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	hs := Coefficients(15*r - (phi + a));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,7);
	"det";
	D := Determinant(J);
	"det finished";
	I := ideal<Rc | [e-D] cat hs>;
	"eliminate";
	return EliminationIdeal(I, {a,e});
end intrinsic;

intrinsic Testje3(p::RngIntElt) -> SeqEnum
{}
	Rc<c1,c2,c3,c4,c5,c6,c7,a,e> := PolynomialRing(GF(p), 9);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	hs := Coefficients(15*r - (phi + a));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,7);
	D := Determinant(J);
	I := ideal<Rc | [e-D] cat hs>;
	//return EliminationIdeal(I, 7: Al := "Direct");
	return I;
end intrinsic;

intrinsic Testje257(a::RngElt) -> SeqEnum
{}
	Rc<[c]> := PolynomialRing(Parent(a), 8);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant(x*(x^3+2*x+1)*(x^4+2*x^3+2),
		t - (c[1]+c[2]*x+c[3]*x^2+c[4]*x^3+c[5]*x^4+c[6]*x^5+c[7]*x^6+c[8]*x^7));
	phi1 := 4*t^5*(14+14*t+20*t^2+25*t^3);
	phi2 := 4*t-1;
	return Coefficients(100*r - (phi1 - a*phi2));
end intrinsic;

intrinsic CloseSolution(f::SeqEnum[RngMPolElt], x::ModTupRngElt) -> ModTupRngElt, RngIntElt
{}
	S := Parent(x);
	R := BaseRing(S);
	m := #R;
	p := Factorization(m)[1][1];
	e := Factorization(m)[1][2];
	
	SZ := RSpace(Z, Rank(S));
	for d := 0 to e do
		T := Integers(p^d);
		ST := RSpace(T, Rank(S));
		k := m / p^d;
		for y in ST do
			vs := [Valuation(c,p) : c in Evaluate(f, Eltseq(SZ!x + k*SZ!y)) | c ne 0];
			if forall {v : v in vs | v ge e} then
				return y, d;
			end if;
		end for;
	end for;
end intrinsic;

intrinsic pAdicDistance(x::SeqEnum, y::SeqEnum, p::RngIntElt) -> RngRatElt
{The l^1 distance induced by the p-adic norm}
	return &+ [p^(-Valuation(Z!(x[i] - y[i]), p)) : i in [1..#x]];
end intrinsic;

intrinsic HenselLiftSingleClose(f::SeqEnum[RngMPolElt], x::ModTupRngElt, m::RngIntElt, M::RngIntElt) -> BoolElt, .
{Lifts a solution x of f modulo m = p^k to a single solution of f modulo p^2k}
	p := Factorization(M)[1][1];
	d := Factorization(M)[1][2];
	SZ := RSpace(Integers(), #f);
	xZ := SZ!x;
	exp := 1;
	for e := 1 to d do
		Se := RSpace(Integers(p^e), #f);
		if exists {c : c in f | Valuation(Evaluate(c, Eltseq(SZ!Se!xZ)), p) lt e} then
			exp := e-2;
			break;
		end if;
	end for;
	if exp+2 eq d then
		return true, x;
	else
		x;
		RSpace(Integers(p^exp), #f)!xZ;
		exp;
		return HenselLiftSingle(f, RSpace(Integers(p^exp), #f)!xZ, p^exp, M);
	end if;
end intrinsic;