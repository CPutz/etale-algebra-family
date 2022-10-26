Q := Rationals();

intrinsic Separant(f::RngUPolElt) -> RngIntElt
{Returns the separant of f}
	return Separant(f, f);
end intrinsic;

intrinsic Separant(f::RngUPolElt, g::RngUPolElt) -> RngIntElt
{Returns the separant of f with respect to g}
	R := BaseRing(Parent(f));
	require BaseRing(Parent(g)) eq R: "Argument 1 and 2 must be defined over the same ring.";
	if ISA(Type(R), RngUPol) then
		return SeparantUPol(f, g);
	elif ISA(Type(R), RngPad) or ISA(Type(R), FldPad) or ISA(Type(R), RngPadRes) or ISA(Type(R), RngPadResExt) then
		return SeparantRng(f, g);
	else
		error("Polynomials must be defined over a p-adic ring/field or a polynomial ring over a p-adic ring/field.");
	end if;
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt) -> RngIntElt
{Returns the separant of f when f is defined over a p-adic ring/field.}
	return SeparantRng(f, f);
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt, g::RngUPolElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(g, y), 2);

	// Degree of the GCD is the number of common roots of f and g (f and g are separable by assumption)
	d := Degree(GCD(f,g));
	res := res div e^d;

	m, _ := Sup([v[1] : v in ValuationsOfRoots(res)]);
	return m;
end intrinsic;

intrinsic Separant(f::RngUPolElt, p::.) -> RngIntElt
{Returns the separant of f}
	return Separant(f, f, p);
end intrinsic;

intrinsic Separant(f::RngUPolElt, g::RngUPolElt, p::.) -> RngIntElt
{Returns the separant of f with respect to g}
	R := BaseRing(Parent(f));
	require BaseRing(Parent(g)) eq R: "Argument 1 and 2 must be defined over the same ring.";
	if ISA(Type(R), RngUPol) then
		return SeparantUPol(f, g);
	elif ISA(Type(R), RngInt) or ISA(Type(R), FldRat) then
		return SeparantRng(f, g, p);
	elif ISA(Type(R), FldNum) then
		return SeparantFldNum(f, g, p);
	else
		error("Polynomials must be defined over Z, Q or a polynomial ring over Z or Q.");
	end if;
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(g, y), 2);

	// Degree of the GCD is the number of common roots of f and g (f and g are separable by assumption)
	d := Degree(GCD(f,g));
	res := res div e^d;

	m, _ := Sup([v[1] : v in ValuationsOfRoots(res, p)]);
	return m;
end intrinsic;

intrinsic SeparantFldNum(f::RngUPolElt, g::RngUPolElt, p::PlcNumElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(g, y), 2);

	// Degree of the GCD is the number of common roots of f and g (f and g are separable by assumption)
	d := Degree(GCD(f,g));
	res := res div e^d;

	m, _ := Sup([v[1] : v in ValuationsOfRoots(res, Ideal(p))]);
	return m;
end intrinsic;

intrinsic SwitchVariables(f::RngUPolElt) -> RngUPolElt
{For a polynomial f in K[x][y] switches x and y}
	require ISA(Type(BaseRing(Parent(f))), RngUPol): "Argument 1 must be defined over R[x][y] for some ring R";
	S := Parent(f);
	R := BaseRing(S);
	T := PolynomialRing(BaseRing(R), 2);
	phi1 := hom<R -> T | T.1>;
	phi2 := hom<S -> T | phi1, T.2>;
	phi3 := hom<T -> S | S.1, R.1>;
	return phi3(phi2(f));
end intrinsic;

intrinsic SeparantUPol(f::RngUPolElt) -> .
{Returns the general separant polynomial of f when f is defined over a polynomial ring in one variable}
	return SeparantUPol(f, f);
end intrinsic;

intrinsic SeparantUPol(f::RngUPolElt, g::RngUPolElt) -> .
{Returns the general separant polynomial of f wrt g when f is defined over a polynomial ring in one variable}
	S := Parent(f);
	t := S.1;
	T<x,y> := PolynomialRing(S,2);
	res := Resultant(Resultant(t - Evaluate(Derivative(f),x) * (x-y), Evaluate(f, x), x), Evaluate(g, y), y);
	return ConstantCoefficient(res);
end intrinsic;

intrinsic SeparantMPol(f::RngMPolElt, v::MPolElt) -> .
{The general separant polynomial of f with respect to v}
	return SeparantMPol(f, f, v);
end intrinsic;

intrinsic SeparantMPol(f::RngMPolElt, g::RngMPolElt, v::MPolElt) -> .
{}
	S := Parent(f);
	T<x,y> := PolynomialRing(S,2);
	res := Resultant(Resultant(v - Evaluate(Derivative(f, v), v, x) * (x-y), Evaluate(f, v, x), x), Evaluate(g, v, y), y);
	//return SwitchVariables(ConstantCoefficient(res));
	return ConstantCoefficient(res);
end intrinsic;

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x> := PolynomialRing(S);
	df := Derivative(f);
	res := S!Resultant(e - Evaluate(df, x) * Evaluate(g, x), Evaluate(f, x));

	// Degree of the GCD is the number of common roots of f and g (f and g are separable by assumption)
	d := Degree(GCD(f,g));
	res := res div e^d;

	m, _ := k * Valuation(R!k) + Sup([v[1] : v in ValuationsOfRoots(res)]);
	return m;
end intrinsic;

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::PlcNumElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x> := PolynomialRing(S);
	df := Derivative(f);
	res := S!Resultant(e - Evaluate(df, x) * Evaluate(g, x), Evaluate(f, x));

	// Degree of the GCD is the number of common roots of f and g (f and g are separable by assumption)
	d := Degree(GCD(f,g));
	res := res div e^d;

	m, _ := k * Valuation(R!k, p) + Sup([v[1] : v in ValuationsOfRoots(res, Ideal(p))]);
	return m;
end intrinsic;