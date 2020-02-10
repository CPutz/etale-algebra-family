intrinsic EtaleTest1(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, c::RngElt, delta::RngElt)
{}
	S<s> := PolynomialRing(Parent(f));
	F := f^k - s*g;
	df := Derivative(f);
	dg := Derivative(g);

	_,_,Es := Factorization(Evaluate(F, c) : Extensions := true);
	K := Es[1]`Extension;

	R,phi := ChangeRing(Parent(f), K);
	Fc := phi(Evaluate(F, c));
	rc := Roots(Fc)[1,1];

	rf := ClosestRoot(phi(f), rc);

	Qp := BaseRing(Parent(f));
	p := Prime(Qp);
	B := [x * delta : x in [1..(p-1)]];

	L := [];

	for d in B do
		F2 := phi(Evaluate(F, c * d^k));

		dF2 := Derivative(F2);
		x0 := rf + Evaluate(phi(f), rc) / Evaluate(phi(df), rf) * d;
		Valuation(Evaluate(F2, x0));
		for i := 1 to 4 do
			x0 := x0 - Evaluate(F2, x0) / Evaluate(dF2, x0);
		end for;
		x := ClosestRoot(F2, x0);
		[Valuation(x - ro[1]) : ro in Roots(F2)]; //There is only one root closest to x

		e := d * Evaluate(phi(f), rc) / Evaluate(phi(df), rf);

		ddf := Derivative(df);
		dddf := Derivative(ddf);
		ddg := Derivative(dg);

		ft := Evaluate(phi(f), rf);
		dft := Evaluate(phi(df), rf);
		ddft := Evaluate(phi(ddf), rf);
		dddft := Evaluate(phi(dddf), rf);
		fa := Evaluate(phi(f), rc);
		gt2 := Evaluate(phi(g), rf);
		dgt := Evaluate(phi(dg), rf);
		ddgt := Evaluate(phi(ddg), rf);
		ga := Evaluate(phi(g), rc);
		dga := Evaluate(phi(dg), rc);

		"nieuwe gok:";
		h1 := fa / dft;
		h2 := fa^2 * (dft * dgt - 2 * ga * ddft) / (2 * ga * dft^3);
		h3 := - c * (3 * dft^2 * dgt^2 + 36 * ga * dft * dgt * ddft - 48 * ga^2 * ddft^2 - 12 * ga * dft^2 * ddgt + 16 * ga^2 * dft * dddft) / (16 * ga * dft^5);
		l2 := (rf + h1 * d + h2 * d^2);
		Valuation(Evaluate(F2, l2));
		2*Valuation(Evaluate(Derivative(F2), l2));
		2*Valuation(Evaluate(Derivative(F2), l2)) - Valuation(Evaluate(F2, l2));
		
		"precisie gok:";
		Valuation(rf - x);
		Valuation(rf + h1 * d - x);
		Valuation(rf + h1 * d + h2 * d^2 - x);
		Valuation(rf + h1 * d + h2 * d^2 + h3 * d^3 - x);

		"valuaties hi:";
		Valuation(h1);
		Valuation(K!d);
		Valuation(h1 * d);
		Valuation(h2 * d^2);
		Valuation(h3 * d^3);

		"test:";
		dF2 := Derivative(F2);
		ddF2 := Derivative(dF2);
		Valuation(Evaluate(dF2, x));
		Valuation(Evaluate(ddF2, x));
		Valuation(Evaluate(F2, x) - Evaluate(F2, rf + h1 * d));
		//Valuation((Evaluate(F2, rc) - Evaluate(F2, l2) - (Evaluate(F2,)));

		"Newton test:";
		x0 := rf + h1 * d;
		for i := 1 to 4 do
			i;
			Valuation(x - x0);
			Valuation(Evaluate(F2, x0));
			Valuation(Evaluate(dF2, x0));
			"";
			x0 := x0 - Evaluate(F2, x0) / Evaluate(dF2, x0);
		end for;
		Valuation(x - x0);
		Valuation(Evaluate(F2, x0));
		Valuation(Evaluate(dF2, x0));

		"";
	end for;

	//[(l1 - l2) : l1, l2 in L | l1 ne l2];
end intrinsic;

intrinsic EtaleTest2(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, c::RngElt, delta::RngElt)
{}
	S<s> := PolynomialRing(Parent(f));
	F := f^k - s*g;
	df := Derivative(f);
	dg := Derivative(g);

	_,_,Es := Factorization(Evaluate(F, c) : Extensions := true);
	K := Es[1]`Extension;

	R,phi := ChangeRing(Parent(f), K);
	Fc := phi(Evaluate(F, c));
	rc := Roots(Fc)[1,1];

	rf := ClosestRoot(phi(f), rc);

	Qp := BaseRing(Parent(f));
	p := Prime(Qp);
	B := [x * delta : x in [1..(p-1)]];

	"degree of K:";
	Degree(K, Qp);

	L := [];

	for d in B do
		F2 := phi(Evaluate(F, c * d^k));
		"number of roots of F2:";
		#Roots(F2);

		dft := Evaluate(phi(df), rf);
		fa := Evaluate(phi(f), rc);
		dF2 := Derivative(F2);
		h1 := fa / dft;

		"Newton test:";
		x0 := rf + h1 * d;
		Valuation(Evaluate(F2, rf));
		Valuation(Evaluate(F2, x0));
		Valuation(Evaluate(dF2, x0));
		Valuation(Evaluate(Derivative(dF2), x0));
		Valuation(Evaluate(Derivative(Derivative(dF2)), x0));
		[Valuation(ro[1] - x0) : ro in Roots(F2)];

		for i := 1 to 3 do
			Valuation(Evaluate(F2, x0));
			x0 := x0 - Evaluate(F2, x0) / Evaluate(dF2, x0);
		end for;
		Valuation(Evaluate(F2, x0));
		Valuation(Evaluate(dF2, x0));
		Valuation(Evaluate(Derivative(dF2), x0));
		Valuation(Evaluate(Derivative(Derivative(dF2)), x0));

		[Valuation(ro[1] - x0) : ro in Roots(F2)];

		"";
	end for;
end intrinsic;

intrinsic ClosestRoot(f::RngUPolElt, r::RngElt) -> RngElt
{}
	rs := Roots(f);
	ds := [Valuation(r - rf[1]) : rf in rs];
	d := Max(ds);
	i := Index(ds, d);
	return rs[i,1];
end intrinsic;

intrinsic ValuationDiffRoots(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, s::RngElt) -> Tup
{}
	F := f^k - s*g;
	K := SplittingField(F);
	roots := Roots(F, K);
	R,phi := ChangeRing(Parent(f), K);
	return <[Valuation(x[1] - y[1]) : x, y in roots | x ne y and ClosestRoot(phi(f), x[1]) eq ClosestRoot(phi(f), y[1])],
			[Valuation(x[1] - y[1]) : x, y in roots | x ne y and ClosestRoot(phi(f), x[1]) ne ClosestRoot(phi(f), y[1])]>;
end intrinsic;

intrinsic ValuationDiffTests(k::RngIntElt, s::RngElt, n::RngIntElt, M::RngIntElt, N::RngIntElt)
{}
	K := Parent(s);
	R<t> := PolynomialRing(K);
	for i in [1..N] do
		fs := Factorization(R!RandomIntegerPolynomial(M, n));
		for f in fs do
			d := Random(0,k*Degree(f[1])-1);
			g := R!RandomIntegerPolynomial(M,d);
			if not ValuationDiffTest(f[1], g, k, s) then
				printf "Fail for f=%o, g=%o, k=%o and s=%o", f[1], g, k, s;
			end if;
		end for;
	end for;
end intrinsic;

intrinsic ValuationDiffTest(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, s::RngElt) -> BoolElt
{}
	F := f^k - s*g;
	K := SplittingField(F);
	roots := Roots(F, K);
	R,phi := ChangeRing(Parent(f), K);
	[Valuation(x[1] - y[1]) : x, y in roots | x ne y and ClosestRoot(phi(f), x[1]) eq ClosestRoot(phi(f), y[1])];
	return #Set([Valuation(x[1] - y[1]) : x, y in roots | x ne y and ClosestRoot(phi(f), x[1]) eq ClosestRoot(phi(f), y[1])]) eq 1;
end intrinsic;

intrinsic RandomIntegerPolynomial(M::RngIntElt, n::RngIntElt) -> RngUPolElt
{Returns a monic polynomial of degree n with coefficient uniformly distributed in [-M,M].}
	return PolynomialRing(Integers()) ! ([ Random(-M, M) : i in [1..n]] cat [1]);
end intrinsic;

intrinsic ValuationTest1(k::RngIntElt, s::RngElt, n::RngIntElt, M::RngIntElt, N::RngIntElt)
{}
	K := Parent(s);
	R<t> := PolynomialRing(K);
	for i in [1..N] do
		fs := Factorization(R!RandomIntegerPolynomial(M, n));
		for f in fs do
			d := Random(0,k*Degree(f[1])-1);
			g := R!RandomIntegerPolynomial(M,d);
			F := f[1]^k - s*g;
			L := SplittingField(F);
			S,phi := ChangeRing(R, L);
			fL := phi(f[1]);
			roots := Roots(F, L);
			for r in roots do
				th := ClosestRoot(fL, r[1]);
				Valuation((r[1] - th)^k - s*Evaluate(g, th) / Evaluate(Derivative(fL), th)^k) / Degree(L, K);
			end for;
		end for;
	end for;
end intrinsic;

intrinsic ValuationTest2(k::RngIntElt, s::RngElt, n::RngIntElt, M::RngIntElt, N::RngIntElt)
{}
	K := Parent(s);
	R<t> := PolynomialRing(K);
	for i in [1..N] do
		fs := Factorization(R!RandomIntegerPolynomial(M, n));
		for f in fs do
			d := Random(0,k*Degree(f[1])-1);
			g := R!RandomIntegerPolynomial(M,d);
			F := f[1]^k - s*g;
			L := SplittingField(F);
			S,phi := ChangeRing(R, L);
			fL := phi(f[1]);
			roots := Roots(F, L);
			for r in roots do
				th := ClosestRoot(fL, r[1]);
				Valuation(Evaluate(g, th) - Evaluate(g, r[1])) / Degree(L, K);
			end for;
		end for;
	end for;
end intrinsic;