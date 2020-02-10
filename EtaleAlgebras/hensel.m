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
		//y; v; N;
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
	return Coefficients(15*r - (phi + 2^20*a));
end intrinsic;

intrinsic Testje2(R::Rng) -> SeqEnum
{}
	Rc<c1,c2,a,e> := PolynomialRing(R, 4);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x^2-2),
		t - (c1+c2*x));
	phi := t^2;
	hs := Coefficients(r - (phi - 2*a^2));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,2);
	D := Determinant(J);
	return hs,D;
end intrinsic;

intrinsic Testje2a(R::Rng) -> SeqEnum
{}
	Rc<c1,c2,c3,a,e> := PolynomialRing(R, 5);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x^2+2*x+2)*(x+1),
		t - (c1+c2*x+c3*x^2));
	hs := Coefficients(r - (t^2*(t+1)+2^5*a^2));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,3);
	D := Determinant(J);
	return hs,D;
end intrinsic;

intrinsic Testje3(R::Rng) -> SeqEnum
{}
	Rc<c1,c2,c3,c4,c5,c6,c7,a,e> := PolynomialRing(R, 9);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant((x+1)*(x^2+x+1)*(x^4+x+1),
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6));
	phi := 15*t^7 - 35*t^6 + 21*t^5;
	psi := -ReciprocalPolynomial(Evaluate(phi - (2*a)^5, 2*a*t) div (2*a)^5);
	hs := Coefficients(r - psi);
	J := ColumnSubmatrix(JacobianMatrix(hs),1,7);
	//"det";
	D := Determinant(J);
	return hs,D;
	//"det finished";
	//I := ideal<Rc | [e-D] cat hs>;
	//"eliminate";
	//return EliminationIdeal(I, {a,e});
end intrinsic;

intrinsic Testje4(p::RngIntElt) -> SeqEnum
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

intrinsic Testje5() -> SeqEnum
{}
	Rc<c0,c1,c2,c3> := PolynomialRing(Q, 4);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant(x^4 + 2*x^3 + 2*x^2 + 2,
		t - (c0 + c1*x + c2*x^2 + c3*x^3));
	phi := 5*t^4 + 28*t^3 + 70*t^2 + 140*t - 35;
	return Coefficients(5*r - phi);
end intrinsic;

intrinsic Testje257(R::Rng) -> SeqEnum
{}
	Rc<c1,c2,c3,c4,c5,c6,c7,c8,a,e> := PolynomialRing(R, 10);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	r := Resultant(x*(x^3+2*x+1)*(x^4+2*x^3+2),
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6+c8*x^7));
	phi1 := 4*t^5*(14+14*t+20*t^2+25*t^3);
	phi2 := 4*t-1;
	hs := Coefficients(100*r - (phi1 - a*phi2));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,8);
	D := Determinant(J);
	return hs,D;
end intrinsic;

intrinsic Testje257a(R::Rng) -> SeqEnum
{}
	Rc<c1,c2,c3,c4,c5,c6,c7,c8,a,e,p> := PolynomialRing(R, 11);
	Rt<t> := PolynomialRing(Rc);
	Rx<x> := PolynomialRing(Rt);
	psix := -35 + 140*x + 70*x^2 + 28*x^3 + 5*x^4;
	psit := -35 + 140*t + 70*t^2 + 28*t^3 + 5*t^4;
	r := Resultant(psix^2 - a^2 * x,
		t - (c1+c2*x+c3*x^2+c4*x^3+c5*x^4+c6*x^5+c7*x^6+c8*x^7));
	hs := Coefficients(r - 5^12*(psit^2 - p^2 * a^2 * t));
	J := ColumnSubmatrix(JacobianMatrix(hs),1,8);
	D := Determinant(J);
	return hs,D;
end intrinsic;

intrinsic Testje357() -> .
{}
	printf "Initialization\n";
	CZ,DZ := Testje3(Z);
	FZ := Factorization(DZ);
	return Testje357(CZ,FZ);
end intrinsic;

intrinsic Testje357(CZ, FZ) -> .
{}
	RZ := Parent(CZ[1]);

	vs := [];
	for F in FZ do
		f := F[1];
		printf "Factor "; PrintTrunc(f,50);
		v := FindValuation(f, CZ, [1,1,1,1,1,1,1]);
		printf "Valuation %o\n", v;
		Append(~vs, v);
	end for;
	return vs;
end intrinsic;

intrinsic FindValuation(F, C, vs) -> RngIntElt
{}
	p := 2;

	RZ := Parent(F);
	n := Rank(RZ);
	ez := Name(RZ,n);

	R := ChangeRing(RZ, GF(p));
	a := Name(R,n-1);
	e := Name(R,n);

	rel := [(R.i)^2-R.i : i in [1..(n-2)]];
	coe := hom<R -> RZ | [R.i : i in [1..n]]>;

	I := ideal<R | [R!x : x in [ez-F] cat C] cat rel>;
	E := EliminationIdeal(I, {a,e});

	if e + 1 in E or e + a + 1 in E then
		return 0;
	else
		Ec := EliminationIdeal(I, Set([R.i : i in [1..(n-2)]]));
		Basis(Ec);
		Basis(EliminationIdeal(ideal<R | [R!x : x in C] cat rel>,Set([R.i : i in [1..(n-2)]])));
		printf "%o\n", Basis(E);
		E1 := [g : g in Basis(Ec) | TotalDegree(g) eq 1];
		E1;
		read accept, "Accept? (y/n/split i)";
		if #accept ge 5 and Substring(accept, 1, 5) eq "split" then
			i := StringToInteger(Substring(accept, 7, 9));
			cZi := coe(RZ.i);
			vsn := vs;
			vsn[i] +:= 1;
			//TODO: do for other p than 2
			printf "c%o = 0\n", i;
			C2 := [Evaluate(c, cZi, 0) div Content(Evaluate(c, cZi, 0)) : c in C | Evaluate(c, cZi, 0) ne 0];
			F2 :=  Evaluate(F, cZi, 0);
			v := Valuation(Content(F2), p);
			printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 0, v, vsn;
			F2 div:= Content(F2);
			v0 := v + FindValuation(F2, C2, vsn);

			printf "c%o = 1\n", i;
			C2 := [Evaluate(c, cZi, 1) div Content(Evaluate(c, cZi, 1)) : c in C | Evaluate(c, cZi, 1) ne 0];
			F2 :=  Evaluate(F, cZi, 1);
			v := Valuation(Content(F2), p);
			printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 1, v, vsn;
			F2 div:= Content(F2);
			v1 := v + FindValuation(F2, C2, vsn);

			return Max(v0, v1);
		elif accept eq "y" then
			return 0;
		else
			if not IsEmpty(E1) then
				read index, "Choose an element of E";
				if index eq "" then
					index := 1;
				else
					index := StringToInteger(index);
				end if;
				g1 := E1[index];
				ci := LeadingMonomial(g1);

				i := -1;
				for j in [1..(n-2)] do
					if R.j eq ci then
						i := j;
					end if;
				end for;
				vsn := vs;
				vsn[i] +:= 1;

				di := (g1-c*ci)/c where c := Coefficient(g1,ci,1);
				cZi := coe(ci);
				dZi := coe(di);
				C2 := [Evaluate(c, cZi, 2*cZi - dZi) div Content(Evaluate(c, cZi, 2*cZi - dZi)) : c in C];
				F2 :=  Evaluate(F, cZi, 2*cZi - dZi);
				v := Valuation(Content(F2), p);
				printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 2*cZi - dZi, v, vsn;
				F2 div:= Content(F2);
				return v + FindValuation(F2, C2, vsn);
			else
				printf "no reductions...\n";
				Error("");
				return -1;
			end if;
		end if;
	end if;

	Error("");
	return -1;
end intrinsic;

intrinsic Testje357_2(CZ, FZ: max_depth := 10, max_div := 2) -> .
{}
	RZ := Parent(CZ[1]);

	vs := [];
	for F in FZ do
		f := F[1];
		printf "Factor "; PrintTrunc(f,50);
		v, tree := FindValuation2(f, CZ, [1,1,1,1,1,1,1], max_depth, max_div);
		printf "Valuation %o, tree %o\n", v, tree;
		Append(~vs, ExtendedReals()!v);
	end for;
	return vs;
end intrinsic;

intrinsic FindValuation2(F, C, vs, max_depth, max_div) -> RngIntElt, .
{}
	p := 2;

	RZ := Parent(F);
	n := Rank(RZ);
	ez := Name(RZ,n);

	R := ChangeRing(RZ, GF(p));
	a := Name(R,n-1);
	e := Name(R,n);

	rel := [(R.i)^2-R.i : i in [1..(n-2)]];
	coe := hom<R -> RZ | [R.i : i in [1..n]]>;

	I := ideal<R | [R!x : x in [ez-F] cat C] cat rel>;
	E := EliminationIdeal(I, {a,e});

	if 1 in E then
		return 0, "x";
	elif e + 1 in E or e + a + 1 in E then
		return 0, <>;
	else
		minv, mini := Min(vs);
		if minv ge max_depth then
			return Infinity(), <>;
		end if;
		Ic := ideal<R | [R!x : x in C] cat rel>;
		Ec := EliminationIdeal(Ic, Set([R.i : i in [1..(n-2)]]));
		E1 := [g : g in Basis(Ec) | TotalDegree(g) eq 1];

		for g1 in E1 do
			vars := Monomials(g1 - ConstantCoefficient(g1));
			for ci in vars do
				i := Index(Exponents(ci),1);
				if vs[i] - minv lt max_div then
					vsn := vs;
					vsn[i] +:= 1;
					di := (g1-c*ci)/c where c := Coefficient(g1,ci,1);
					cZi := coe(ci);
					dZi := coe(di);
					C2 := [Evaluate(c, cZi, 2*cZi - dZi) div Content(Evaluate(c, cZi, 2*cZi - dZi)) : c in C];
					F2 :=  Evaluate(F, cZi, 2*cZi - dZi);
					v := Valuation(Content(F2), p);
					printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 2*cZi - dZi, v, vsn;
					F2 div:= Content(F2);
					va, tree := FindValuation2(F2, C2, vsn, max_depth, max_div);
					vn := v + va;
					return vn, <i, di, v, tree>;
				end if;
			end for;
		end for;

		//split on mini
		i := mini;
		cZi := coe(RZ.i);
		vsn := vs;
		vsn[i] +:= 1;
		//TODO: do for other p than 2
		C2 := [Evaluate(c, cZi, 2*cZi) div Content(Evaluate(c, cZi,2*cZi)) : c in C | Evaluate(c, cZi,2*cZi) ne 0];
		F2 :=  Evaluate(F, cZi, 2*cZi);
		v0p := Valuation(Content(F2), p);
		printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 2*cZi, v0p, vsn;
		F2 div:= Content(F2);
		va0, tree0 := FindValuation2(F2, C2, vsn, max_depth, max_div);
		v0 := v0p + va0;

		C2 := [Evaluate(c, cZi,2*cZi-1) div Content(Evaluate(c, cZi,2*cZi-1)) : c in C | Evaluate(c, cZi,2*cZi-1) ne 0];
		F2 :=  Evaluate(F, cZi,2*cZi-1);
		v1p := Valuation(Content(F2), p);
		printf "Substitution %o <- %o (valuation +%o) (%o)\n", cZi, 2*cZi - 1, v1p, vsn;
		F2 div:= Content(F2);
		va1, tree1 := FindValuation2(F2, C2, vsn, max_depth, max_div);
		v1 := v1p + va1;

		return Max(v0, v1), <i, <v0p,tree0>, <v1p,tree1>>;
	end if;
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