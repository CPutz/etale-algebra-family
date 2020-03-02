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
	elif ISA(Type(R), RngPad) or ISA(Type(R), FldPad) then
		return SeparantRng(f, f);
	else
		error("Polynomials must be defined over a p-adic ring/field or a polynomial ring over a p-adic ring/field.");
	end if;
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt, g::RngUPolElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	error if BaseRing(Parent(g)) ne R, "Argument 1 and 2 must be defined over the same ring.";

	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(g, y), 2);
	
	if f eq g then
		res := res div e^Degree(f);
	end if;

	//TODO: make Max([-Infinity()] cat ...) into Sup
	m, _ := Max([-Infinity()] cat [v[1] : v in ValuationsOfRoots(res)]);

	//TODO: add a precision bound here
	//res := CleanupPolynomial(res);

	//N := NewtonPolygon(res);
	//return -Min(Slopes(N));

	//TODO: make Max([-Infinity()] cat ...) into Sup
	//m, _ := Max([-Infinity()] cat [v[1] : v in ValuationsOfRoots(res) | v[1] lt Infinity()]);
	return m;
end intrinsic;

intrinsic SeparantRng(f::RngUPolElt) -> RngIntElt
{Returns the separant of f when f is defined over a p-adic ring/field.}
	return SeparantRng(f, f);
end intrinsic;

intrinsic Separant(f::RngUPolElt, p::RngIntElt) -> RngIntElt
{Returns the separant of f}
	return Separant(f, f, p);
end intrinsic;

intrinsic Separant(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngIntElt
{Returns the separant of f with respect to g}
	R := BaseRing(Parent(f));
	require BaseRing(Parent(g)) eq R: "Argument 1 and 2 must be defined over the same ring.";
	if ISA(Type(R), RngUPol) then
		return SeparantUPol(f, g, p);
	elif ISA(Type(R), RngInt) or ISA(Type(R), FldRat) then
		return SeparantRng(f, f, p);
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

	//TODO: figure out when to throw away Infinity
	//TODO: make Max([-Infinity()] cat ...) into Sup
	m, _ := Max([-Infinity()] cat [v[1] : v in ValuationsOfRoots(res, p) | v[1] lt Infinity()]);
	return m;
end intrinsic;

/*intrinsic SeparantUPol(f::RngUPolElt) -> RngIntElt
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

intrinsic SeparantUPol(f::RngUPolElt, p::RngIntElt) -> .
{Returns the separant of f when f is defined over a polynomial ring in one variable
over a p-adic ring/field.}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	res := S!Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(f, y), 2);

	return MyValuationsOfRoots(res, p, p);
end intrinsic;*/

intrinsic SeparantUPol(f::RngUPolElt, p::RngIntElt) -> .
{Returns the separant of f when f is defined over a polynomial ring in one variable
over the rationals.}
	Fs<s> := FunctionField(Q);
	V := ValuationRing(Fs, PolynomialRing(Q).1);
	T<e,x,y> := PolynomialRing(V,3);
	f := ChangeRing(f, V);
	df := Derivative(f);
	res := Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 2), Evaluate(f, y), 3);
	//res;
	//S!res;
	res := UnivariatePolynomial(res);

	return res;
end intrinsic;

intrinsic SeparantUPolOld(f::RngUPolElt, p::RngIntElt) -> RngIntElt
{Returns the separant of f when f is defined over a polynomial ring in one variable
over the rationals.}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(S,2);
	df := Derivative(f);
	r := Resultant(Resultant(e - Evaluate(df, x) * (x - y), Evaluate(f, x), 1), Evaluate(f, y), 2);
	res := S!r;
	res := res div e^(Degree(TrailingTerm(res)));

	res2 := S![TrailingTerm2(c) : c in Coefficients(res)];
	dif := res - res2;

	B := 0;
	for i := 0 to Degree(dif) do
		c := Coefficient(dif, i);
		for d := 1 to Degree(c) do
			v := Valuation(Coefficient(c, d), p);
			b := (1 - v) / d;
			B := Max(b, B);
		end for;
	end for;

	ds := 0;
	c0 := Coefficient(res2, 0);
	vcs := [];
	for i := 1 to Degree(res2) do
		ci := Coefficient(res2, i);
		if ci ne 0 then
			d := c0 div ci;
			vc := Valuation(LeadingCoefficient(d), p);
			//printf "%o + %o * v(s)\n", vc / i, Degree(d) / i;
			ds := Max(Degree(d) / i, ds);
			Append(~vcs, vc / i);
		end if;
	end for;

	if ds eq 0 then
		m,_ := Max(vcs);
		return m;
	else
		return -1;
	end if;
end intrinsic;

intrinsic CleanupPolynomial(p::RngUPolElt) -> RngUPolElt
{}
	S := Parent(p);
	//R := BaseRing(S);
	return S![Cleanup(c) : c in Coefficients(p)];
end intrinsic;

intrinsic Cleanup(c::RngElt) -> RngElt
{}
	if RelativePrecision(c) eq 0 then
		return 0;
	else 
		return c;
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