declare verbose EtaleAlg, 1;

Z := Integers();
Q := Rationals();
EtRF := recformat< E : EtAlg, N : SeqEnum, Noo : SeqEnum >;

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
	return MaxValuationOfRootsMPol(ValuationsInRootsOfUPol(f,g));
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	return MaxValuationOfRootsMPol(ValuationsInRootsOfUPol(f,g), p);
end intrinsic;

intrinsic MinValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{Returns the minimal valuation of f at roots of g}
	return MinValuationOfRootsMPol(ValuationsInRootsOfUPol(f,g));
end intrinsic;

intrinsic MinValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the minimal valuation of f at roots of g}
	return MinValuationOfRootsMPol(ValuationsInRootsOfUPol(f,g), p);
end intrinsic;

intrinsic MaxValuationDiffRoots(f::RngUPolElt) -> RngUPolElt, RngIntElt
{}
	return MaxValuationDiffRoots(f, f);
end intrinsic;

intrinsic MaxValuationDiffRoots(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(E,2);
	res := ConstantCoefficient(Resultant(Resultant(e - (x - y), Evaluate(f, x), x), Evaluate(g, y), y));
	return res;
	return MaxValuationOfRootsMPol(res div e^Valuation(res));
end intrinsic;

intrinsic MaxValuationDiffRoots(f::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	return MaxValuationDiffRoots(f, f, p);
end intrinsic;

intrinsic MaxValuationDiffRoots(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<x,y> := PolynomialRing(E,2);
	res := ConstantCoefficient(Resultant(Resultant(e - (x - y), Evaluate(f, x), x), Evaluate(g, y), y));
	return MaxValuationOfRootsMPol(res div e^Valuation(res), p);
end intrinsic;

intrinsic BoundPower(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := Max(0, k * Separant(f));
	M := Max(M, k * Separant(f, g));
	M := Max(M, k * Separant(f, Derivative(g)));

	vs := [v[1] : v in ValuationsInRootsOfQuotient(Derivative(f)^k * g^(k-1), Derivative(g)^k, f) | v[1] ne Infinity()];
	M := Max(M, Sup(vs));

	//for i := 0 to k*Degree(f) do
	//	M := Max(M, Valuation(Coefficient(f^k, i)) - Valuation(Coefficient(g, i)));
	//end for;

	return M;
end intrinsic;

intrinsic BoundPower(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := Max(0, k * Separant(f, p));
	M := Max(M, k * Separant(f, g, p));
	M := Max(M, k * Separant(f, Derivative(g), p));

	vs := [v[1] : v in ValuationsInRootsOfQuotient(Derivative(f)^k * g^(k-1), Derivative(g)^k, f, p) | v[1] ne Infinity()];
	M := Max(M, Sup(vs));

	//for i := 0 to k*Degree(f) do
	//	M := Max(M, Valuation(Coefficient(f^k, i), p) - Valuation(Coefficient(g, i), p));
	//end for;

	return M;
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngMPolElt, v::RngIntResElt, p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500) -> .
{}
	Qp := pAdicField(p, Precision);
	R := PolynomialRing(Qp, 2);
	return EtaleAlgebraFamily(R!F, v : D := D, Precision := Precision, FZ := F);
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngUPolElt, p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0) -> SeqEnum
{}
	R := Parent(F); //Z[s][t] or Q[s][t]
	S := BaseRing(R); //Z[s] or Q[s]
	//require ISA(Type(BaseRing(S)), RngInt) or ISA(Type(BaseRing(S)), FldRat):
	//	"Argument 1 must be defined over Z or Q";
	require ISA(Type(BaseRing(S)), FldRat): "Argument 1 must be defined over Q";

	s := S.1;
	t := R.1;
	K := pAdicField(p, Precision);
	OK := Integers(K);
	X := pAdicNbhds(K);
	pi := K!p;

	//TODO: make monic and integral
	lc := LeadingCoefficient(LeadingCoefficient(F));
	F /:= lc; //creates rounding errors
	while exists {cs : cs in Coefficients(ct), ct in Coefficients(F) | Valuation(cs,p) lt 0} do
		F := p^Degree(F) * Evaluate(F, t/p);
	end while;

	//TODO: quite bad
	while exists (cs) {cs : cs in Coefficients(ct), ct in Coefficients(F) | Denominator(cs) gt 1} do
		d := Denominator(cs);
		F := d^Degree(F) * Evaluate(F, t/d);
	end while;

	vprintf EtaleAlg: "computing general separant\n";
	gen_sep := SeparantUPol(F) div t^Degree(F);

	vprintf EtaleAlg: "computing discriminant\n";
	disc := Discriminant(F);
	roots := [r[1] : r in Roots(disc, K) | IsIntegral(r[1])];
	roots_Q := [r[1] : r in Roots(disc, Q) | Valuation(r[1],p) ge 0];
	require #roots eq #roots_Q: "The roots in Qp of the discriminant of Argument 1 should be in Q";

	SK<sK> := PolynomialRing(K);
	RK<tK> := PolynomialRing(SK);
	FK := RK!F;

	OKp := quo<OK | pi^Precision>;
	SOKp := PolynomialRing(OKp);
	ROKp := PolynomialRing(SOKp);
	Nbhds_disc := []; // The neighborhoods around the roots of the discriminant
	Nbhds_oo := [];

	for r in roots_Q do	
		// Evaluate F at s = r
		f := Evaluate(SwitchVariables(FK), r);
		// The coefficient of s in F
		g := Coefficient(SwitchVariables(FK), 1);

		fs,unit := Factorization(f);
		f_hats := [f div fi[1]^fi[2] : fi in fs];
		d,cs := XGCD(f_hats);
		//assert that sum_i cs[i] * f_hats[i] = d
		assert forall {c : c in Coefficients(d - &+[fc[1]*fc[2] : fc in Zip(cs, f_hats)]) | K!0 in c};

		//assert that d is the constant 1
		assert K!0 in (unit - 1);
		assert Degree(d) eq 0;
		d := ConstantCoefficient(d);
		assert K!0 in (d - 1);

		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in Zip(cs, fs)];

		// Construction of the Fi = fi^ki + s*ri
		Fis := [Evaluate(fr[1][1]^fr[1][2], tK) + sK * Evaluate(fr[2], tK) : fr in Zip(fs, rs)];

		// Translate the variable s in F by r
		F_r := SwitchVariables(Evaluate(SwitchVariables(F), t + r));

		sep_r := SwitchVariables(Evaluate(SwitchVariables(gen_sep), t + r));
		v_sep, b_sep := MaxValuationOfRootsMPol(sep_r,p);
		vprintf EtaleAlg: "max sep: %o\n", v_sep;

		FK_r := SwitchVariables(Evaluate(SwitchVariables(FK), tK + r));

		// The valuation of difference between FK_r and &*Fis is >= 2v(s) - min_val
		dif := FK_r - &*Fis;
		min_val_dif := Min([Valuation(cs) : cs in Coefficients(ct), ct in Coefficients(dif)]);
		L<x> := PolynomialRing(Q);
		v_dif := 2*x + min_val_dif;
		vprintf EtaleAlg: "min diff: %o\n", v_dif;

		// When is dif > sep?
		assert (LeadingCoefficient(v_dif) gt LeadingCoefficient(v_sep));
		b1 := Floor(Roots(v_dif - v_sep)[1][1] + 1);
		vprintf EtaleAlg: "dif > sep if v(s) >= %o\n", b1;

		b_power := -Infinity();
		for fr in Zip(fs, rs) do
			b_power := Max(b_power, BoundPower(fr[1][1], fr[2], fr[1][2]));
		end for;
		// Make into inclusive bound
		b_power := Floor(b_power + 1);
		vprintf EtaleAlg: "power bound: %o\n", b_power;

		bound := Max(Max(Max(0, b_sep), b1), b_power);
		vprintf EtaleAlg: "bound (%o): %o\n", r, bound;

		//TODO: bounds for individual factors

		Append(~Nbhds_disc, r + O(pi^bound));

		k := LCM([fi[2] : fi in fs]);
		vprintf EtaleAlg: "k = %o\n", k;
		v := k * Ceiling(bound / k);
		v_power := 2*Valuation(K!k) + 1;
		OKmOKk := quo<OK | pi^v_power>; // OK / (OK)^k
		// representatives for OK* / (OK*)^k would be sufficient here
		//TODO: something separate with 0 here...?
		Nbhds_oo cat:= [CreatePAdicNbhd(X, OKp!r, (K!c) * pi^(v + w), k) : c in OKmOKk, w in [0..k-1]];
	end for;

	vprintf EtaleAlg: "computing nbhds\n";

	gen_sep_K := RK!SwitchVariables(gen_sep);
	min_val_s := Min([Valuation(cs, p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	// Split up in neighborhoods
	Nbhds := [O(K!1)];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	repeat
		Nbhds_new := [];
		for N in Nbhds do
			if exists { Nd : Nd in Nbhds_disc | Nd in N } then
				Nbhds_new cat:= Subdivide(N, AbsolutePrecision(N) + 1);
			else
				vals := ValuationsOfRoots(Evaluate(gen_sep_K, N));
				mu := Sup([v[1] : v in vals]) - min_val_s;

				if mu lt AbsolutePrecision(N) then
					Append(~Nbhds_end, N);
				elif exists { Nd : Nd in Nbhds_disc | N in Nd } then
					//Do nothing since N is contained in one of the neighborhoods around a root of the discriminant
				else //if sep lt Infinity() then
					Nbhds_new cat:= Subdivide(N, Floor(mu + 1));
				end if;
			end if;
		end for;
		Nbhds := Nbhds_new;

		// Filter
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(CreatePAdicNbhd(X, OKp!N, pi^AbsolutePrecision(N), 1), Filter)];
	until IsEmpty(Nbhds);

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [CreatePAdicNbhd(X, OKp!n, pi^AbsolutePrecision(n), 1) : n in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, Filter)];

	vprintf EtaleAlg: "computing etale algebras for %o nbhds\n", #Nbhds;
	E := EtaleAlgebraListIsomorphism2(F, Nbhds : D := D);

	return E;
end intrinsic;





intrinsic EtaleAlgebraFamily2(F::RngUPolElt, p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0) -> SeqEnum
{}
	R := Parent(F); //Z[s][t] or Q[s][t]
	S := BaseRing(R); //Z[s] or Q[s]
	//require ISA(Type(BaseRing(S)), RngInt) or ISA(Type(BaseRing(S)), FldRat):
	//	"Argument 1 must be defined over Z or Q";
	//require ISA(Type(BaseRing(S)), FldRat): "Argument 1 must be defined over Q";

	s := S.1;
	t := R.1;
	K := BaseRing(S);
	OK := Integers(K);
	X := pAdicNbhds(K);
	pi := K!p;

	//TODO: make monic and integral
	lc := LeadingCoefficient(LeadingCoefficient(F));
	F /:= lc; //creates rounding errors
	while exists {cs : cs in Coefficients(ct), ct in Coefficients(F) | Valuation(cs) lt 0} do
		F := p^Degree(F) * Evaluate(F, t/p);
	end while;

	vprintf EtaleAlg: "computing discriminant\n";
	disc := Discriminant(F);
	roots := [r[1] : r in Roots(disc, K) | IsIntegral(r[1])];

	SK<sK> := PolynomialRing(K);
	RK<tK> := PolynomialRing(SK);
	FK := RK!F;

	OKp := quo<OK | pi^Precision>;
	SOKp := PolynomialRing(OKp);
	ROKp := PolynomialRing(SOKp);
	Nbhds_disc := []; // The neighborhoods around the roots of the discriminant
	Nbhds_oo := [];

	for r in roots do
		// Evaluate F at s = r
		f := Evaluate(SwitchVariables(FK), r);
		// The coefficient of s in F
		g := Coefficient(SwitchVariables(FK), 1);

		fs,unit := Factorization(f);
		f_hats := [f div fi[1]^fi[2] : fi in fs];

		c,cs := XGCD(f_hats);
		min_val := Min([Valuation(ci) : ci in Coefficients(c), c in cs] cat [0]);
		c *:= pi^min_val;
		cs := [pi^min_val * c : c in cs];
		cs := [LeadingCoefficient(c) : c in cs];

		//assert that sum_i cs[i] * f_hats[i] = d
		d := c;
		assert forall {c : c in Coefficients(c - &+[fc[1]*fc[2] : fc in Zip(cs, f_hats)]) | K!0 in c};

		//TODO: is this assumption needed?
		//assert that d is the constant 1
		assert K!0 in (unit - 1);
		assert Degree(d) eq 0;
		d := ConstantCoefficient(d);
		assert K!0 in (d - 1);

		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in Zip(cs, fs)];

		// Construction of the Fi = fi^ki + s*ri
		Fis := [Evaluate(fr[1][1]^fr[1][2], tK) + sK * Evaluate(fr[2], tK) : fr in Zip(fs, rs)];

		// Translate the variable s in F by r
		F_r := SwitchVariables(Evaluate(SwitchVariables(F), t + r));

		bound := 0;
		for i := 1 to #fs do
			fi := fs[i][1];
			ki := fs[i][2];
			ri := rs[i] / cs[i];
			fi;
			sigf := Separant(fi);
			sigfr := Separant(fi, ri);

		end for;

		Append(~Nbhds_disc, r + O(pi^bound));

		k := LCM([fi[2] : fi in fs]);
		vprintf EtaleAlg: "k = %o\n", k;
		v := k * Ceiling(bound / k);
		v_power := 2*Valuation(K!k) + 1;
		OKmOKk := quo<OK | pi^v_power>; // OK / (OK)^k
		// representatives for OK* / (OK*)^k would be sufficient here
		//TODO: something separate with 0 here...?
		Nbhds_oo cat:= [CreatePAdicNbhd(X, OKp!r, (K!c) * pi^(v + w), k) : c in OKmOKk, w in [0..k-1]];
	end for;

	vprintf EtaleAlg: "computing nbhds\n";

	//gen_sep_K := RK!SwitchVariables(gen_sep);
	//min_val_s := Min([Valuation(cs, p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	// Split up in neighborhoods
	Nbhds := [O(K!1)];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	repeat
		Nbhds_new := [];
		for N in Nbhds do
			if exists { Nd : Nd in Nbhds_disc | Nd in N } then
				Nbhds_new cat:= Subdivide(N, AbsolutePrecision(N) + 1);
			else
				/*vals := ValuationsOfRoots(Evaluate(gen_sep_K, N));
				mu := Sup([v[1] : v in vals]) - min_val_s;

				if mu lt AbsolutePrecision(N) then
					Append(~Nbhds_end, N);
				elif exists { Nd : Nd in Nbhds_disc | N in Nd } then
					//Do nothing since N is contained in one of the neighborhoods around a root of the discriminant
				else //if sep lt Infinity() then
					Nbhds_new cat:= Subdivide(N, Floor(mu + 1));
				end if;*/
			end if;
		end for;
		Nbhds := Nbhds_new;

		// Filter
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(CreatePAdicNbhd(X, OKp!N, pi^AbsolutePrecision(N), 1), Filter)];
	until IsEmpty(Nbhds);

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [CreatePAdicNbhd(X, OKp!n, pi^AbsolutePrecision(n), 1) : n in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, Filter)];

	vprintf EtaleAlg: "computing etale algebras for %o nbhds\n", #Nbhds;
	E := EtaleAlgebraListIsomorphism2(F, Nbhds : D := D);

	return E;
end intrinsic;





intrinsic Subdivide(x::FldPadElt, n::RngIntElt) -> SeqEnum
{}
	r := AbsolutePrecision(x);
	if n le r then
		return [x];
	else
		K := Parent(x);
		OK := Integers(K);
		pi := UniformizingElement(OK);
		R := quo<OK | pi^(n - r)>;
		S := quo<OK | pi^n>;
		return [K!((S!x) + pi^r * y) : y in R];
	end if;
end intrinsic;

intrinsic MaxValuationOfRootsMPol(res::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	R := Parent(res); //K[s][t]
	S := BaseRing(R); //K[s]
	e := R.1;
	s := S.1;

	if ConstantCoefficient(res) eq 0 then
		return Infinity(), -Infinity();
	end if;

	i := 0;
	while not CorrectAux(ConstantCoefficient(res),p) do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;
	
	repeat
		changed := false;
		L<x> := PolynomialRing(Q);
		vals := [<c[1], ValuationUPol(c[2],p)> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
		slopes := [<(vals[1][2] - v[2]) / (v[1] - vals[1][1]), v[1]> : v in vals[2..#vals]];
		a := Max([Coefficient(c[1],1) : c in slopes]);
		b := Max([ConstantCoefficient(c[1]) : c in slopes | Coefficient(c[1],1) eq a]);
		
		index := Min([c[2] : c in slopes | c[1] eq a*x + b]);
		if not CorrectAux(Coefficient(res,index),p) then
			res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
			i +:= 1;
			changed := true;
		end if;
	until CorrectAux(Coefficient(res,index),p) and not changed;

	//TODO: check that this is correct
	return a*x+b - i*a, i;
end intrinsic;

intrinsic MinValuationOfRootsMPol(res::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	R := Parent(res); //K[s][t]
	S := BaseRing(R); //K[s]
	e := R.1;
	s := S.1;

	if ConstantCoefficient(res) eq 0 then
		return Infinity(), -Infinity();
	end if;

	i := 0;
	while not CorrectAux(LeadingCoefficient(res),p) do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;

	repeat
		changed := false;
		L<x> := PolynomialRing(Q);
		vals := [<c[1], ValuationUPol(c[2],p)> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
		slopes := [<(v[2] - vals[#vals][2]) / (vals[#vals][1] - v[1]), v[1]> : v in vals[1..#vals-1]];
		a := Min([Coefficient(c[1],1) : c in slopes]);
		b := Min([ConstantCoefficient(c[1]) : c in slopes | Coefficient(c[1],1) eq a]);

		index := Max([c[2] : c in slopes | c[1] eq a*x + b]);
		if not CorrectAux(Coefficient(res,index),p) then
			res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
			i +:= 1;
			changed := true;
		end if;
	until CorrectAux(Coefficient(res,index),p) and not changed;

	//TODO: check that this is correct
	return a*x+b - i*a, i;
end intrinsic;

intrinsic ValuationOfRootsMPolStraight(res::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	v_max, b_max := MaxValuationOfRootsMPol(res,p);
	v_min, b_min := MinValuationOfRootsMPol(res,p);

	assert v_max eq v_min;

	return v_max, Max(b_max, b_min);
end intrinsic;

intrinsic ValuationUPol(f::RngUPolElt, p::RngIntElt) -> RngUPolElt
{}
	L<x> := PolynomialRing(Q);
	if f eq 0 then
		return Infinity();
	else
		a := Valuation(f);
		return a*x + Valuation(Coefficient(f, a), p);
	end if;
end intrinsic;

intrinsic CorrectAux(f::RngUPolElt, p::RngIntElt) -> BoolElt
{Returns true if 0 is the only root of f in the ring of integers}
	if f eq 0 then
		return true;
	end if;
	t := Parent(f).1;
	f := f div (t^(Z!Valuation(f)));
	return forall {v : v in ValuationsOfRoots(f,p) | v[1] lt 0};
end intrinsic;


intrinsic MaxValuationOfRootsMPol(res::RngUPolElt) -> RngUPolElt, RngIntElt
{}
	R := Parent(res); //K[s][t]
	S := BaseRing(R); //K[s]
	K := BaseRing(S);
	p := UniformizingElement(K);
	e := R.1;
	s := S.1;

	if ConstantCoefficient(res) eq 0 then
		return Infinity(), -Infinity();
	end if;

	i := 0;
	while not CorrectAux(ConstantCoefficient(res)) do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;
	
	repeat
		changed := false;
		L<x> := PolynomialRing(Q);
		vals := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
		slopes := [<(vals[1][2] - v[2]) / (v[1] - vals[1][1]), v[1]> : v in vals[2..#vals]];
		a := Max([Coefficient(c[1],1) : c in slopes]);
		b := Max([ConstantCoefficient(c[1]) : c in slopes | Coefficient(c[1],1) eq a]);
		index := Min([c[2] : c in slopes | c[1] eq a*x + b]);
		if not CorrectAux(Coefficient(res,index)) then
			res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
			i +:= 1;
			changed := true;
		end if;
	until CorrectAux(Coefficient(res,index)) and not changed;

	//TODO: check that this is correct
	return a*x+b - i*a, i;
end intrinsic;

intrinsic MinValuationOfRootsMPol(res::RngUPolElt) -> RngUPolElt, RngIntElt
{}
	R := Parent(res); //K[s][t]
	S := BaseRing(R); //K[s]
	K := BaseRing(S);
	p := UniformizingElement(K);
	e := R.1;
	s := S.1;

	if ConstantCoefficient(res) eq 0 then
		return Infinity(), -Infinity();
	end if;

	i := 0;
	while not CorrectAux(LeadingCoefficient(res)) do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;

	repeat
		changed := false;
		L<x> := PolynomialRing(Q);
		vals := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
		slopes := [<(v[2] - vals[#vals][2]) / (vals[#vals][1] - v[1]), v[1]> : v in vals[1..#vals-1]];
		a := Min([Coefficient(c[1],1) : c in slopes]);
		b := Min([ConstantCoefficient(c[1]) : c in slopes | Coefficient(c[1],1) eq a]);
		index := Max([c[2] : c in slopes | c[1] eq a*x + b]);
		if not CorrectAux(Coefficient(res,index)) then
			res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
			i +:= 1;
			changed := true;
		end if;
	until CorrectAux(Coefficient(res,index)) and not changed;

	//TODO: check that this is correct
	return a*x+b - i*a, i;
end intrinsic;

intrinsic ValuationOfRootsMPolStraight(res::RngUPolElt) -> RngUPolElt, RngIntElt
{}
	v_max, b_max := MaxValuationOfRootsMPol(res);
	v_min, b_min := MinValuationOfRootsMPol(res);

	assert v_max eq v_min;

	return v_max, Max(b_max, b_min);
end intrinsic;

intrinsic ValuationUPol(f::RngUPolElt) -> RngUPolElt
{}
	L<x> := PolynomialRing(Q);
	if f eq 0 then
		return Infinity();
	else
		a := Valuation(f);
		return a*x + Valuation(Coefficient(f, a));
	end if;
end intrinsic;

intrinsic CorrectAux(f::RngUPolElt) -> BoolElt
{Returns true if 0 is the only root of f in the ring of integers}
	if f eq 0 then
		return true;
	end if;
	t := Parent(f).1;
	f := f div (t^(Z!Valuation(f)));
	return forall {v : v in ValuationsOfRoots(f) | v[1] lt 0};
end intrinsic;



FactorizationStructureList := function(L)
    return Sort([<Degree(Ki[1]), Ki[2]> : Ki in L]);
end function;

intrinsic EtaleAlgebraListIsomorphism2(F::RngUPolElt, B::SeqEnum
  : D := LocalFieldDatabase()) -> SeqEnum[Tup]
{Creates a list of etale algebra given a polynomial F in K[s][t] where K is a local field
and a list B of parameter values for s}
    if IsEmpty(B) then
        return [];
    end if;

    Res := [];
    OK := ISA(Type(Universe(B)), PadNbhd) select AmbientSpace(Parent(B[1])) else RingOfIntegers(Parent(B[1]));
    //R := PolynomialRing(OK);
    Fs := PolynomialRing(PolynomialRing(OK)) ! SwitchVariables(F);

    //TODO: use MakeMonicIntegral only once
    factorizations := [<Factorization(MakeMonicIntegral(Evaluate(Fs, OK!Representative(s)))),
    	Evaluate(Fs, OK!Representative(s)), s> : s in B];
    Fstructures := {@ FactorizationStructureList(fac[1]) : fac in factorizations @};
    Fss := [[F : F in factorizations | FactorizationStructureList(F[1]) eq Fstruct] : Fstruct in Fstructures];

    for Fss0 in Fss do
    	res := [];
    	for FP in Fss0 do
            found := false;
            for i := 1 to #res do
                if IsDefiningPolynomialEtale(res[i][1], FP[1]) then
                    found := true;
                	found_i := i;
                    break;
                end if;
            end for;
            if found then //add witness
            	Append(~res[found_i][2], FP[3]);
            else
                Append(~res, <EtaleAlgebra(FP[2]: D := D), [FP[3]]>);
            end if;
        end for;

    	Res cat:= res;
    end for;

    return Res;
end intrinsic;

intrinsic Representative(N::FldPadElt) -> FldPadElt
{}
	return N;
end intrinsic;



intrinsic GeneralizeNbhds(S::SeqEnum[PadNbhdElt]) -> SeqEnum[PadNbhdElt]
{}
	if IsEmpty(S) then
		return [];
	end if;
	
	X := Parent(S[1]);

	S_new := [];
	cks := {@ <Middle(s), Exponent(s)> : s in S @};
	for ck in cks do
		Ss := GeneralizeNbhds([Radius(s) : s in S | Middle(s) eq ck[1] and Exponent(s) eq ck[2]]);
		S_new cat:= [CreatePAdicNbhd(X, ck[1], s, ck[2]) : s in Ss];
	end for;

	S1 := [s : s in S_new | Exponent(s) eq 1];
	while exists (s1) { s : s in S1 |
			exists { t : t in S1 | t ne s and
				Valuation(Middle(s) - Middle(t)) ge Valuation(Radius(t)) and
				Valuation(Radius(s)) ge Valuation(Radius(t)) } } do
		Exclude(~S1, s1);
		Exclude(~S_new, s1);
	end while;

	return S_new;
end intrinsic;

intrinsic GeneralizeNbhds(S::SeqEnum[FldPadElt]) -> SeqEnum[FldPadElt]
{}
	if IsEmpty(S) then
		return [];
	end if;
	
	R := Parent(S[1]);
	p := UniformizingElement(R);
	rs := ResidueSystem(R);
	repeat
		change := false;
		Stemp := S;
		for x in Stemp do
			prec := AbsolutePrecision(x);

			if prec eq 0 then
				return [x];
			elif exists {y : y in S | AbsolutePrecision(y) lt prec and x in y} then
				Exclude(~S, x);
				change := true;
			elif forall {r : r in rs | exists { y : y in S | x + r * p^(prec-1) in y } } then
				Exclude(~S, x);
				Include(~S, x + O(p^(prec-1)));
				change := true;
			end if;
		end for;
	until change eq false;

	return S;
end intrinsic;

intrinsic 'in'(x::FldPadElt, y::FldPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;

intrinsic 'in'(x::RngPadElt, y::RngPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;
