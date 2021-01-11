QQ := Rationals();
ZZ := Integers();
R<x> := PolynomialRing(QQ);

function myheight(x);
	m := Max([Abs(c) : c in Eltseq(x)]);
	return m;
end function;

intrinsic PolynomialHeight(f::.) -> .
{}
	m := Max([myheight(c) : c in Coefficients(f)]);
	return m;
end intrinsic;

intrinsic ParametrizationHeight(par::SeqEnum) -> RngIntElt
{}
	m := Max([PolynomialHeight(c) : c in par]);
	return m;
end intrinsic;

intrinsic MyImproveParametrization2(param::MapSch) -> MapSch
{}
	C := Codomain(param);
	P<X,Y> := CoordinateRing(Domain(param));
	k := Dimension(AmbientSpace(C)) + 1;
	K<a> := BaseRing(P);

	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	g2 := -a^5 - a^4 - a^3 + a^2 + 2*a + 2;
	g2_2 := -a^5 + a^4 - 2*a + 3;
	g2_3 := -a^4 + a^3 - 2*a^2 + a - 2;
	g3 := a^3 - 2;
	g5 := a;
	g7 := a^4 - 2*a^3 + 2*a^2 - 3*a + 3;
	Xs := [(-1)^e1 * u2^e2 * u3^e3 * u4^e4 * g2^e5 * g5^e6 * g7^e7 : e1,e2,e3,e4,e5,e6,e7 in [0,1]];

	param := MyImproveParametrization(param);
	h := ParametrizationHeight([param([X,Y])[i] : i in [1..k]]);

	repeat
		"it";
		changed := false;
		param_new_new := param;
		for x,y in Xs do
			point := param([x,y]);
			param_new := MyImproveParametrization(Parametrization(C,point));
			h_new := ParametrizationHeight([param_new([X,Y])[i] : i in [1..k]]);
			if h_new lt h then
				h_new;
				h := h_new;
				param_new_new := param_new;
			end if;
		end for;
		param := param_new_new;
	until not changed;

	h;
	return param;
end intrinsic;

intrinsic MyImproveParametrization(param::MapSch) -> MapSch
{}
	P<X,Y> := CoordinateRing(Domain(param));
	K<a> := BaseRing(P);
	k := Dimension(AmbientSpace(Codomain(param))) + 1;
	param_new := [param([X,Y])[i] : i in [1..k]];
	coeffs := [c : c in Coefficients(d), d in param_new];
	mons := [m : m in Monomials(d), d in param_new];
	denom := LCM([Denominator(Norm(c)) : c in coeffs]);
	num := GCD([Numerator(Norm(c)) : c in coeffs]);
	//scale variables
	/*for p in Factorization(denom * num) do
		for P in Decomposition(K,p[1]) do
			for var in [X,Y] do
				val := Floor(Min([Valuation(mc[2],P[1]) / Degree(mc[1],var) : mc in Zip(mons,coeffs) | Degree(mc[1],var) gt 0]));
				if val ne 0 then
					_,g := IsPrincipal(Ideal(P[1]));
					param_new := [Evaluate(d, var, g^(-val)*var) : d in param_new];
				end if;
			end for;
		end for;
	end for;*/

	coeffs := [c : c in Coefficients(d), d in param_new];
	denom := LCM([Denominator(Norm(c)) : c in coeffs]);
	num := GCD([Numerator(Norm(c)) : c in coeffs]);
	//scale coefficients
	for p in Factorization(denom * num) do
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coeffs]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				param_new := [g^(-val) * d : d in param_new];
			end if;
		end for;
	end for;

	//preferred representatives of OK*/(OK*)^2
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u2^e2 * u3^e3 * u4^e4 : e2,e3,e4 in [-1..1]];
	// Scale by units
	h := ParametrizationHeight(param_new);
	repeat
		changed := false;
		param_new_tmp := param_new;
		//scale variables
		/*for u in Us do
			for var in [X,Y] do
				param_new_new := [Evaluate(c, var, var/u) : c in param_new];
				if  h gt ParametrizationHeight(param_new_new) then
					h := ParametrizationHeight(param_new_new);
					param_new_tmp := param_new_new;
					changed := true;
				end if;
			end for;
		end for;
		param_new := param_new_tmp;*/
		//scale coefficients
		for u in Us do
			param_new_new := [c / u : c in param_new];
			if  h gt ParametrizationHeight(param_new_new) then
				h := ParametrizationHeight(param_new_new);
				param_new_tmp := param_new_new;
				changed := true;
			end if;
		end for;
		param_new := param_new_tmp;
	until not changed;

	return map< Domain(param) -> Codomain(param) | param_new >;
end intrinsic;

intrinsic FindParametrization(C::CrvCon) -> Pt
{}
	K := BaseRing(C);
	_,x0 := HasRationalPoint(C);
	par0 := Parametrization(C,x0);

	B := IntegralBasis(K);
	I := [-1..1];
	Car := CartesianPower(I, #B);
	Xs := [ &+[cb[1]*cb[2] : cb in Zip(TupSeq(c),B)] : c in Car];

	x1 := x0;
	min := MyHeight(x0[1]);
	min;
	for x in Xs do
		for y in Xs do
			h := MyHeight(par0([x,y])[1]);
			if min gt h then
				min := h;
				x1 := par0([x,y])[1];
				min;
				x1;
			end if;
		end for;
	end for;

	return x1;
end intrinsic;

intrinsic FindParametrization2(C::CrvCon) -> Pt
{}
	K := BaseRing(C);
	_,x0 := HasRationalPoint(C);

	B := IntegralBasis(K);
	I := [-1..1];
	Car := CartesianPower(I, #B);
	Xs := [ &+[cb[1]*cb[2] : cb in Zip(TupSeq(c),B)] : c in Car];

	repeat
		found := false;
		min := MyHeight(x0[1]);
		min;
		x0;
		par0 := Parametrization(C,C!x0);
		for x in Xs do
			for y in Xs do
				if min gt MyHeight(par0([x,y])[1]) then
					x0 := par0([x,y]);
					found := true;
					break x;
				end if;
			end for;
		end for;
	until not found;

	return x0;
end intrinsic;

intrinsic Coverings(u::FldNumElt) -> SeqEnum
{}
	K<a> := Parent(u);
	P2<X,Y,Z> := ProjectiveSpace(K,2);
	_<t> := PolynomialRing(K);
	C0 := Conic(P2, Y^2 - u*(X^2 - X*Z - Z^2));

	//preferred representatives of OK*/(OK*)^2
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u1^e1 * u2^e2 * u3^e3 * u4^e4 : e1,e2,e3,e4 in [0,1]];

	g7 := a^4 - 2*a^3 + 2*a^2 - 3*a + 3;

	res := [];
	if HasRationalPoint(C0) then
		par := MyImproveParametrization(Parametrization(C0));

		P := par([X,Y])[1];
		Q := par([X,Y])[2];
		R := par([X,Y])[3];

		r := Evaluate(Resultant(P, Q, X), [0,1,0]);
		Bs := Us;
		//add 7
		Bs := Bs cat [b * g7 : b in Bs];
		for p in Factorization(ZZ!Norm(r)) do
			for P in Decomposition(K,p[1]) do
				if Valuation(r, P[1]) ne 0 then
					_,g := IsPrincipal(Ideal(P[1]));
					Bs := Bs cat [b * g : b in Bs];
				end if;
			end for;
		end for;

		for b in Bs do
			CX := Conic(P2, P - b * Z^2);
			CZ := Conic(P2, R - 7*u * b * Z^2);

			if HasRationalPoint(CX) and HasRationalPoint(CZ) then
				Append(~res, b);
			end if;
		end for;
	end if;

	return res;
end intrinsic;

intrinsic ConicMap(u::FldNumElt, b::FldNumElt) -> MapSch
{}
	K := Parent(u);
	P2<X,Y,Z> := ProjectiveSpace(K,2);
	_<t> := PolynomialRing(K);
	C := HyperellipticCurve(u*(t^4 - (7*u)*t^2 - (7*u)^2));
	C0 := Conic(P2, Y^2 - u*(X^2 - X*Z - Z^2));
	par := MyImproveParametrization(Parametrization(C0));

	P := par([X,Y])[1];
	Q := par([X,Y])[2];
	R := par([X,Y])[3];

	CX := Conic(P2, P - b * Z^2);
	CZ := Conic(P2, R - 7*u * b * Z^2);

	U := MyImproveParametrization(Parametrization(CX));
	V := MyImproveParametrization(Parametrization(CZ));

	S := Curve(P2, U([X,Z])[1] * V([Y,Z])[2] - U([X,Z])[2] * V([Y,Z])[1]);

	return map < S -> C |
		[U([X,Z])[3] * V([Y,Z])[1],
		 par([U([X,Z])[1], U([X,Z])[2]])[2] * V([Y,Z])[1]^2 / b,
		 U([X,Z])[1] * V([Y,Z])[3]] >;
end intrinsic;

intrinsic DescentConicMap(u::FldNumElt, phi::MapSch) -> MapSch
{}
	S := Domain(phi);
	f := DefiningPolynomial(S);
	R<X,Y,Z> := Parent(f);
	K := BaseRing(R);
	_<t> := PolynomialRing(K);

	g := Evaluate(Discriminant(f,1), [0,t,1]);
	H := HyperellipticCurve(g);

	a0 := Term(f,X,2) div X^2;
	a1 := Term(f,X,1) div X;

	StoH := map< S -> H | [Y*Z, (2*a0*X + a1)*Z, Z^2]>;

	b0 := Coefficient(g,0);
	b1 := Coefficient(g,1);
	b2 := Coefficient(g,2);
	Coefficient(g,4) / b0;
	Coefficient(g,3) / b1;
	assert Coefficient(g,4) eq b0 * u^2;
	assert Coefficient(g,3) eq b1 * u;
	P2<X,Y,Z> := ProjectiveSpace(K,2);
	//C := Conic(P2, Y^2 - (b0*X^2 + b1*X*Z + (b2 - 2*b0*u)*Z^2));
	//HtoC := map< H -> C | [u*X^2 + Z^2, Y, X*Z]>;

	_,s := IsSquare((b2*b0 - 2*b0^2*u - b1^2 / 4) / u);
	C := Conic(P2, X^2 + u*Z^2 - b0*Y^2);
	HtoC := map< H -> C | [b0*(u*X^2 + Z^2) + b1/2*(X*Z),Y,s*X*Z]>;

	//TODO: construct a variety which C maps to and a map back to H?
	//TODO: test whether taking a diagonal form gives better parametrizations

	return StoH, HtoC;

	/*par := MyImproveParametrization(Parametrization(C));
	P3<X,Y,Z,W> := ProjectiveSpace(K,3);
	P := par([X,Y])[1];
	Q := par([X,Y])[2];
	R := par([X,Y])[3];
	D := Conic(P3, [P - (u*Z^2 + W^2), R - Z*W]);

	return map <D -> H | [ Z, Q, W ] >;*/
end intrinsic;

intrinsic CoprimeRepresentative(coords::SeqEnum) -> SeqEnum
{}
	K<a> := Parent(coords[1]);
	denom := LCM([Denominator(Norm(c)) : c in coords]);
	num := GCD([Numerator(Norm(c)) : c in coords]);
	coords_new := coords;
	for p in Factorization(denom * num) do
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coords]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				coords_new := [g^(-val) * c : c in coords_new];
			end if;
		end for;
	end for;

	//preferred representatives of OK*/(OK*)^2
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u2^e2 * u3^e3 * u4^e4 : e2,e3,e4 in [-1..1]];
	// Scale by units
	h := Max([myheight(c) : c in coords_new]);
	repeat
		changed := false;
		coords_new_tmp := coords_new;
		for u in Us do
			coords_new_new := [c / u : c in coords_new];
			if  h gt Max([myheight(c) : c in coords_new_new]) then
				h := Max([myheight(c) : c in coords_new_new]);
				coords_new_tmp := coords_new_new;
				changed := true;
			end if;
		end for;
		coords_new := coords_new_tmp;
	until not changed;

	return coords_new;
end intrinsic;

intrinsic CoprimeRepresentative(p::Pt) -> SeqEnum
{}
	return CoprimeRepresentative(Coordinates(p));
end intrinsic;

intrinsic SimplifyUpToSquares(coords::SeqEnum) -> SeqEnum
{}
	K<a> := Parent(coords[1]);
	denom := LCM([Denominator(Norm(c)) : c in coords]);
	num := GCD([Numerator(Norm(c)) : c in coords]);
	coords_new := coords;
	for p in Factorization(denom * num) do
		p;
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coords]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				coords_new := [g^(-2*Floor(val/2)) * c : c in coords_new];
			end if;
		end for;
	end for;

	//preferred representatives of OK*/(OK*)^2
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u2^e2 * u3^e3 * u4^e4 : e2,e3,e4 in [-1..1]];
	// Scale by units
	h := Max([myheight(c) : c in coords_new]);
	repeat
		changed := false;
		coords_new_tmp := coords_new;
		for u in Us do
			coords_new_new := [c / u^2 : c in coords_new];
			if  h gt Max([myheight(c) : c in coords_new_new]) then
				h := Max([myheight(c) : c in coords_new_new]);
				coords_new_tmp := coords_new_new;
				changed := true;
			end if;
		end for;
		coords_new := coords_new_tmp;
	until not changed;

	return coords_new;
end intrinsic;

intrinsic Test(u::FldNumElt) -> CrvHyp
{}	
	K := Parent(u);
	R<t> := PolynomialRing(K);
	P2<X,Y,Z> := ProjectiveSpace(K,2);
	C0 := Conic(P2, Y^2 - u*(X^2 - X*(7*Z) - (7*Z)^2));
	par := MyImproveParametrization(Parametrization(C0));
	h := 7*u*par([t,1])[1]*par([t,1])[3];
	return HyperellipticCurve(R!SimplifyUpToSquares(Coefficients(h)));
end intrinsic;

//TODO: move to NumberFields
intrinsic SquarefreePart(a::FldNumElt) -> FldNumElt
{}
	K := Parent(a);
	norm := Norm(a);
	num := Numerator(norm);
	denom := Denominator(norm);
	for p in Factorization(num * denom) do
		for P in Decomposition(K,p[1]) do
			val := Valuation(a,P[1]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				a := a * g^(-2 * Floor(val/2));
			end if;
		end for;
	end for;
	return a;
end intrinsic;

intrinsic ConicMapInverse(p::Pt) -> MapSch
{}
	K := Parent(Coordinates(p)[1]);
	u := LeadingCoefficient(HyperellipticPolynomials(Parent(p)));
	P2<X,Y,Z> := ProjectiveSpace(K,2);

	C0 := Conic(P2, Y^2 - u*(X^2 - X*Z - Z^2));
	par := MyImproveParametrization(Parametrization(C0));
	_,parinv := IsInvertible(par);

	q := C0![p[1]^2, p[2], 7*u*p[3]^2];
	st := CoprimeRepresentative(parinv(q));

	P := par([X,Y])[1];
	Q := par([X,Y])[2];
	R := par([X,Y])[3];
	b := SquarefreePart(Evaluate(P,[st[1],st[2],0]));
	CX := Conic(P2, P - b * Z^2);
	CZ := Conic(P2, R - 7*u * b * Z^2);
	U := MyImproveParametrization(Parametrization(CX));
	V := MyImproveParametrization(Parametrization(CZ));

	_,x := IsPower(Evaluate(P,[st[1],st[2],0]) / b, 2);
	_,z := IsPower(Evaluate(R,[st[1],st[2],0]) / (7*u*b), 2);
	pX := CX![st[1], st[2], x];
	pZ := CZ![st[1], st[2], z];

	S := Curve(P2, U([X,Z])[1] * V([Y,Z])[2] - U([X,Z])[2] * V([Y,Z])[1]);
	_,Uinv := IsInvertible(U);
	_,Vinv := IsInvertible(V);
	uv := Uinv(pX);
	xy := Vinv(pZ);

	return S![uv[1]/uv[2], xy[1]/xy[2], 1], b;
end intrinsic;

function MapCoefficients(f,p);
	R := Parent(f);
	Rp := ResidueClassField(p);
	return PolynomialRing(Rp)![Evaluate(c,p) : c in Coefficients(f)];
end function;

intrinsic LocalSearch(f::RngUPolElt, p::PlcNumElt) -> SeqEnum
{}
	K := BaseRing(f);
	fp := MapCoefficients(f,p);
	Rp := ResidueClassField(p);
	if IsPrimeField(Rp) then
		phi := hom<Rp -> K | >;
	else
		phi := hom<Rp -> K | K.1>;
	end if;

	Cs := [phi(x) : x in Rp | IsPower(Evaluate(fp, x), 2)];

	fr := ReciprocalPolynomial(f);
	frp := MapCoefficients(fr,p);
	//if IsPower(Evaluate(frp, 0), 2) then
	//	printf "potential factor in the denominator: %o\n", p;
	//end if;

	if IsPower(Evaluate(frp, 0), 2) and IsEmpty(Cs) then
		printf "factor in the denominator: %o\n", p;
	end if;

	return Cs;
end intrinsic;

intrinsic LocalSearch(f::RngUPolElt, S::SeqEnum) -> SeqEnum
{}
	K := BaseRing(f);
	res := [];
	Cs := [];
	Ps := [];

	M := 1;
	for i := 1 to #S do
		p := S[i];
		Cp := LocalSearch(f,p);
		if #Cp lt #ResidueClassField(p) then
			Append(~Ps, p);
			Append(~Cs, Cp);
			_,g := IsPrincipal(Ideal(p));
			M *:= g;
		end if;
	end for;
	#Ps;
	for i := 1 to #Ps do
		p := Ps[i];
		Rp := ResidueClassField(p);
		if IsPrimeField(Rp) then
			phi := hom<Rp -> K | >;
		else
			phi := hom<Rp -> K | K.1>;
		end if;
		_,g := IsPrincipal(Ideal(p));
		m := M div g;
		c := m * phi(Evaluate(m, p)^(-1));
		Append(~res, [c * x : x in Cs[i]]);
	end for;

	return [&+TupSeq(x) : x in CartesianProduct(res)], M;
end intrinsic;

intrinsic LocalSieve(f::RngUPolElt, S::SeqEnum : Bound := 10) -> SeqEnum
{}
	K<a> := BaseRing(f);
	X,m := LocalSearch(f, S);
	
	M := Matrix([Eltseq(a^i * m) : i in [0..Degree(K)-1]]);
	L := Lattice(M);
	//B := Basis(L);
	B := HermiteForm(MatrixAlgebra(ZZ,Degree(K))!M);

	L0 := [e1*B[1] + e2*B[2] + e3*B[3] + e4*B[4] + e5*B[5] + e6*B[6] + e7*B[7] : e1,e2,e3,e4,e5,e6,e7 in [-1..1]];

	res := [];
	for x in X do
		vx := Vector(Eltseq(x));
		b := Bound;
		repeat
			P := CloseVectors(L, vx, b);
			b *:= 2;
		until not IsEmpty(P);
		v := P[1,1]; //a vector in L closest to x
		vy := vx - v;
		
		for l in L0 do
			y := K!Eltseq(vy + l);
			if IsSquare(Norm(Evaluate(f, y))) then
				Append(~res, y);
			end if;
		end for;
	end for;

	return res;
end intrinsic;

intrinsic LocalSieve2(f::RngUPolElt, S::SeqEnum : Bound := 10) -> BoolElt, .
{}
	K<a> := BaseRing(f);
	X,m := LocalSearch(f, S);

	M := Matrix([Eltseq(a^i * m) : i in [0..Degree(K)-1]]);
	L := Lattice(M);
	//B := Basis(L);
	B := HermiteForm(MatrixAlgebra(ZZ,Degree(K))!M);

	L0 := [e1*B[1] + e2*B[2] + e3*B[3] + e4*B[4] + e5*B[5] + e6*B[6] + e7*B[7] : e1,e2,e3,e4,e5,e6,e7 in [-1..1]];

	res := [];
	for x in X do
		vx := Vector(Eltseq(x));
		b := Bound;
		repeat
			P := CloseVectors(L, vx, b);
			b *:= 2;
		until not IsEmpty(P);
		v := P[1,1]; //a vector in L closest to x
		vy := vx - v;
		
		for l in L0 do
			y := K!Eltseq(vy + l);
			if IsSquare(Evaluate(f, y)) then
				return true, y;
			end if;
		end for;
	end for;

	return false,"";
end intrinsic;

intrinsic LocalSieve3(f::RngUPolElt, S::SeqEnum) -> BoolElt, .
{}
	K<a> := BaseRing(f);
	X,m := LocalSearch(f, S);
	m;
	#X;

	M := Matrix([Eltseq(a^i * m) : i in [0..Degree(K)-1]]);
	L := Lattice(M);
	B := Basis(L);
	//B := HermiteForm(MatrixAlgebra(ZZ,Degree(K))!M);
	_,N := IsInvertible(MatrixAlgebra(QQ,7)!Matrix(B));

	//L0 := [e1*B[1] + e2*B[2] + e3*B[3] + e4*B[4] + e5*B[5] + e6*B[6] + e7*B[7] : e1,e2,e3,e4,e5,e6,e7 in [-1..1]];
	L0 := [L!0];

	res := [];
	for x in X do
		vx := Vector(Eltseq(x));

		vy := Vector(Matrix([[FractionalPart(c + 1/2) - 1/2 : c in Eltseq((Matrix([Eltseq(x)]) * N)[1])]]) * MatrixAlgebra(QQ,7)!Matrix(B));
		
		for l in L0 do
			y := K!Eltseq(vy + l);
			if IsSquare(Evaluate(f, y)) then
				return true, y;
			end if;
		end for;
	end for;

	return false,"";
end intrinsic;

intrinsic Radical(x::RngIntElt) -> RngIntElt
{}
	if x^2 eq 1 then
		return 1;
	else
		return &*[f[1] : f in Factorization(x)];
	end if;
end intrinsic;

intrinsic MyHeight(x::FldNumElt) -> RngIntElt
{}
	//m := Max([Abs(Numerator(c) * Denominator(c)) : c in Coefficients(MinimalPolynomial(x))]);
	N := Norm(x);
	m := Radical(Numerator(N) * Denominator(N));
	return m;
end intrinsic;

intrinsic NormPolynomial(f::RngUPolElt) -> RngMPolElt
{}
	R<t> := PolynomialRing(QQ);
	L<a,b> := GaloisSplittingField(t^7 - 5);
	z := a/b;

	R<[x]> := PolynomialRing(L,7);
	S := PolynomialRing(QQ,7);

	_,phi := IsSubfield(BaseRing(f), L);
	_,psi := ChangeRing(Parent(f), L, phi);

	return S!&*[Evaluate(psi(f),&+[x[j+1] * (a*z^i)^j : j in [0..6]]) : i in [0..6]];
end intrinsic;

intrinsic NormPolynomial2(f::RngUPolElt) -> RngMPolElt
{}
	f0 := NormPolynomial(PolynomialRing(QQ).1);
	S := PolynomialRing(QQ,7);
	return S!Evaluate(f0, EltseqPolynomial(f));
end intrinsic;

intrinsic EltseqPolynomial(f::RngUPolElt) -> SeqEnum
{}
	K<a> := BaseRing(f);
	R<[x]> := PolynomialRing(K,Degree(K));
	y := &+[x[j+1] * K.1^j : j in [0..Degree(K)-1]];
	fy := Evaluate(f,y);
	Ms := [[c * m : c in Eltseq(MonomialCoefficient(fy,m))] : m in Monomials(fy)];
	X := [&+[c[i] : c in Ms] : i in [1..Degree(K)]];
	return X;
end intrinsic;

intrinsic EltseqPolynomial(f::RngMPolElt) -> SeqEnum
{}
	K<a> := CoefficientRing(Parent(f));
	r := Rank(Parent(f));
	R<[x]> := PolynomialRing(K,r*Degree(K));
	ys := [&+[x[Degree(K)*i + j+1] * K.1^j : j in [0..Degree(K)-1]] : i in [0..r-1]];
	fy := Evaluate(f,ys);
	Ms := [[c * m : c in Eltseq(MonomialCoefficient(fy,m))] : m in Monomials(fy)];
	X := [&+[c[i] : c in Ms] : i in [1..Degree(K)]];
	return X;
end intrinsic;

intrinsic TransformedEltseqPolynomial(f::RngUPolElt, S::SeqEnum) -> SeqEnum, SeqEnum
{}
	K<a> := BaseRing(f);
	g := EltseqPolynomial(f);

	m := &*[g where _,g := IsPrincipal(Ideal(p)) : p in S];

	M := MatrixAlgebra(ZZ,7)!Matrix([Eltseq(a^i * m) : i in [0..Degree(K)-1]]);
	//TODO: the diagonal is assumed to be 1's except the last entry (not guarenteed)
	H := HermiteForm(M);
	H;
	C := Rows(Transpose(H))[Degree(K)];
	diag := Diagonal(H);
	C;
	diag;

	assert forall { i : i in [1..Degree(K)-1] | diag[i+1] mod diag[i] eq 0 };

	R<[x]> := Parent(g[1]);
	sub := [x[i] : i in [1..Rank(R)-1]] cat [x[Rank(R)] + &+[C[i] * x[i] : i in [1..Rank(R)-1]]];
	sub;
	g2 := [Evaluate(gi, sub) : gi in g];

	primes := {@ #PrimeField(ResidueClassField(P)) : P in S @};
	Cps := [];
	for p in primes do
		Ps := [P : P in S | #PrimeField(ResidueClassField(P)) eq p];
		d := &+[InertiaDegree(P) : P in Ps];
		X := [Repeat(0,Degree(K)-d) cat TupSeq(c) : c in CartesianPower([0..p-1], d)];

		Cp := {x : x in X | forall { P : P in Ps | IsSquare(Evaluate(K![Evaluate(gi, x) : gi in g2], P)) } };
		p;
		assert #Ps eq 1;
		1. * #Cp / p^d;
		Append(~Cps, [x[7] : x in Cp]);
	end for;

	return g2, Cps;
end intrinsic;

intrinsic TransformedEltseqPolynomial(f::RngMPolElt, S::SeqEnum) -> SeqEnum, SeqEnum
{}
	K<a> := BaseRing(Parent(f));
	g := EltseqPolynomial(f);
	r := Rank(Parent(f));

	m := &*[g where _,g := IsPrincipal(Ideal(p)) : p in S];

	M := MatrixAlgebra(ZZ,7)!Matrix([Eltseq(a^i * m) : i in [0..Degree(K)-1]]);
	//TODO: the diagonal is assumed to be 1's except the last entry (not guarenteed)
	H := HermiteForm(M);
	H;
	C := Rows(Transpose(H))[Degree(K)];
	diag := Diagonal(H);
	C;
	diag;

	assert forall { i : i in [1..Degree(K)-1] | diag[i+1] mod diag[i] eq 0 };

	R<[x]> := Parent(g[1]);
	sub := &cat[[x[j*Degree(K) + i] : i in [1..Degree(K)-1]] cat [x[(j+1)*Degree(K)] + &+[C[i] * x[j*Degree(K) + i] : i in [1..Degree(K)-1]]] : j in [0..r-1]];
	sub;
	g2 := [Evaluate(gi, sub) : gi in g];

	primes := {@ #PrimeField(ResidueClassField(P)) : P in S @};
	Cps := [];
	for p in primes do
		Ps := [P : P in S | #PrimeField(ResidueClassField(P)) eq p];
		d := &+[InertiaDegree(P) : P in Ps];
		X := [Repeat(0,Degree(K)-d) cat TupSeq(c) : c in CartesianPower([0..p-1], d)];
		X2 := [&cat TupSeq(c) : c in CartesianPower(X,r)];

		Cp := {x : x in X2 | forall { P : P in Ps | IsSquare(Evaluate(K![Evaluate(gi, x) : gi in g2], P)) } };
		p;
		#Ps;
		1. * #Cp / p^(d*r);
		Append(~Cps, <p,[x : x in Cp]>);

		//Cp;
		//Cp := {ZZ!x : x in GF(Norm(Ideal(p))) | IsSquare(Evaluate(K![Evaluate(gi, [0,0,0,0,0,0,ZZ!x]) : gi in g2], p))};
		//Norm(Ideal(p));
		//Cp;
	end for;

	return g2, Cps;
end intrinsic;