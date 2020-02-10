intrinsic Separant(f::RngUPolElt) -> RngElt
{Returns the separant of f}
	R := BaseRing(Parent(f));
	if ISA(Type(R), RngUPol) then
		return SeparantUPol(f);
	elif ISA(Type(R), RngPad) or ISA(Type(R), FldPad) then
		return SeparantRng(f);
	else
		error("Polynomial must be defined over either a p-adic field/ring or a polynomial ring over a p-adic field/ring.");
	end if;
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt) -> RngElt
{Returns the separant of f when f is defined over a p-adic ring/field.}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(f, y), 2);

	//TODO: add a precision bound here
	res := CleanupPolynomial(res);

	N := NewtonPolygon(res);
	return -Min(Slopes(N));
end intrinsic;

intrinsic SeparantUPol(f::RngUPolElt) -> RngElt
{Returns the separant of f when f is defined over a polynomial ring in one variable
over a p-adic ring/field.}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	r := Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(f, y), 2);
	res := S!r;

	//cleanup
	res := CleanupPolynomial(res);
	res := res div e^(Degree(TrailingTerm(res)));

	res2 := S![TrailingTerm2(c) : c in Coefficients(res)];
	dif := CleanupPolynomial(res - res2);

	B := 0;
	for i := 0 to Degree(dif) do
		c := Coefficient(dif, i);
		for d := 1 to Degree(c) do
			v := Valuation(Coefficient(c, d));
			b := (1 - v) / d;
			B := Max(b, B);
		end for;
	end for;

	ds := 0;
	c0 := Coefficient(res2, 0);
	for i := 1 to Degree(res2) do
		ci := Coefficient(res2, i);
		if ci ne 0 then
			d := c0 div ci;
			vc := Valuation(LeadingCoefficient(d));
			printf "%o + %o * v(s)\n", vc / i, Degree(d) / i;
			ds := Max(Degree(d) / i, ds);
		end if;
	end for;

	return res;
end intrinsic;

intrinsic CleanupPolynomial(p::RngUPolElt) -> RngUPolElt
{}
	S := Parent(p);
	R := BaseRing(S);
	return S![R![Cleanup(c) : c in Coefficients(r)] : r in Coefficients(p)];
end intrinsic;

intrinsic Cleanup(c::RngElt) -> RngElt
{}
	if Valuation(c) lt 450 then
		return c;
	else 
		return 0;
	end if;
end intrinsic;

intrinsic TrailingTerm2(c::RngUPolElt) -> RngUPolElt
{}
	if c eq 0 then
		return 0;
	else
		return TrailingTerm(c);
	end if;
end intrinsic;