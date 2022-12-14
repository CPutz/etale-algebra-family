import "utils.m" : sup;

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

	m, _ := sup([v[1] : v in ValuationsOfRoots(res)]);
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

	m, _ := sup([v[1] : v in ValuationsOfRoots(res, p)]);
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

	m, _ := sup([v[1] : v in ValuationsOfRoots(res, Ideal(p))]);
	return m;
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

intrinsic ValuationsInRootsOfUPol(f::RngUPolElt, g::RngUPolElt) -> .
{Returns the general resultant giving the valuations of f at the roots of g}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return res;
end intrinsic;

intrinsic ValuationsInRootsOf(f::RngUPolElt, g::RngUPolElt) -> .
{Returns the valuations of f at the roots of g}
	return ValuationsOfRoots(ValuationsInRootsOfUPol(f,g));
end intrinsic;

intrinsic ValuationsInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> .
{Returns the valuations of f at the roots of g}
	return ValuationsOfRoots(ValuationsInRootsOfUPol(f,g), p);
end intrinsic;

intrinsic ValuationsInRootsOfUPolQuotient(f1::RngUPolElt, f2::RngUPolElt, g::RngUPolElt) -> .
{Returns the general resultant giving the valuations of f1/f2 at the roots of g}
	R := BaseRing(Parent(f1));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	res := Resultant(Evaluate(f2, t) * e - Evaluate(f1, t), Evaluate(g, t));
	return res;
end intrinsic;

intrinsic ValuationsInRootsOfQuotient(f1::RngUPolElt, f2::RngUPolElt, g::RngUPolElt) -> .
{Returns the valuations of f1/f2 at the roots of g}
	return ValuationsOfRoots(ValuationsInRootsOfUPolQuotient(f1,f2,g));
end intrinsic;

intrinsic ValuationsInRootsOfQuotient(f1::RngUPolElt, f2::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> .
{Returns the valuations of f1/f2 at the roots of g}
	return ValuationsOfRoots(ValuationsInRootsOfUPolQuotient(f1,f2,g), p);
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	return Max([x[1] : x in ValuationsOfRoots(ValuationsInRootsOfUPol(f,g))]);
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	return Max([x[1] : x in ValuationsOfRoots(ValuationsInRootsOfUPol(f,g), p)]);
end intrinsic;
