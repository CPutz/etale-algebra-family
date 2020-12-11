QQ := Rationals();
ZZ := Integers();
R<x> := PolynomialRing(QQ);

intrinsic MyImproveParametrization(param::MapSch) -> MapSch
{}
	P<X,Y> := CoordinateRing(Domain(param));
	K := BaseRing(P);
	k := Dimension(AmbientSpace(Codomain(param))) + 1;
	param_new := [param([X,Y])[i] : i in [1..k]];
	coeffs := [c : c in Coefficients(d), d in param_new];
	denom := LCM([Denominator(Norm(c)) : c in coeffs]);
	num := GCD([Numerator(Norm(c)) : c in coeffs]);
	for p in Factorization(denom * num) do
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coeffs]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				param_new := [g^(-val) * d : d in param_new];
			end if;
		end for;
	end for;

	return map< Domain(param) -> Codomain(param) | param_new >;
end intrinsic;

intrinsic Coverings(u::FldNumElt) -> SeqEnum
{}
	K<a> := Parent(u);
	P2<X,Y,Z> := ProjectiveSpace(K,2);
	_<xK> := PolynomialRing(K);
	C := HyperellipticCurve(u*(xK^4 - (7*u)*xK^2 - (7*u)^2));
	C0 := Conic(P2, Y^2 - u*(X^2 - X*Z - Z^2));

	//preferred representatives of OK*/(OK*)^2 here
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u1^e1 * u2^e2 * u3^e3 * u4^e4 : e1,e2,e3,e4 in [0,1]];
	
	res := [];
	if HasRationalPoint(C0) then
		par := MyImproveParametrization(Parametrization(C0));

		P := par([X,Y])[1];
		Q := par([X,Y])[2];
		R := par([X,Y])[3];

		r := Evaluate(Resultant(P, Q, X), [0,1,0]);
		Bs := Us;
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
	_<xK> := PolynomialRing(K);
	C := HyperellipticCurve(u*(xK^4 - (7*u)*xK^2 - (7*u)^2));
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

intrinsic CoprimeRepresentative(p::Pt) -> SeqEnum
{}
	coords := Coordinates(p);
	K := Parent(coords[1]);
	denom := LCM([Denominator(Norm(c)) : c in coords]);
	coords_new := coords;
	for p in Factorization(denom) do
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coords]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				coords_new := [g^(-val) * c : c in coords_new];
			end if;
		end for;
	end for;
	return coords_new;
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
	return [phi(x) : x in Rp | IsPower(Evaluate(fp, x), 2)];
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
	if x eq 0 then
		return 10^6;
	end if;
	//m := Max([Abs(c) : c in Coefficients(MinimalPolynomial(x))]);
	N := Norm(x);
	m := Radical(Numerator(N) * Denominator(N));
	return m;
end intrinsic;