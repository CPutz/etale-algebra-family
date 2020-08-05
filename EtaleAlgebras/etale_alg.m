Z := Integers();
Q := Rationals();
EtRF := recformat< E : EtAlg, N : SeqEnum, Noo : SeqEnum >;

intrinsic ValuationsInRootsOf(f::RngUPolElt, g::RngUPolElt) -> .
{Returns the valuations of f at the roots of g}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return ValuationsOfRoots(res);
end intrinsic;

intrinsic ValuationsInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> .
{Returns the valuations of f at the roots of g}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return ValuationsOfRoots(res, p);
end intrinsic;

intrinsic ValuationsInRootsOfUPol(f::RngUPolElt, g::RngUPolElt) -> .
{Returns the general resultant giving the valuations of f at the roots of g}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return res;
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<t> := PolynomialRing(E);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return MaxValuationOfRootsMPol(res);
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<t> := PolynomialRing(E);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return MaxValuationOfRootsMPol(res, p);
end intrinsic;

intrinsic MinValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{Returns the minimal valuation of f at roots of g}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<t> := PolynomialRing(E);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return MinValuationOfRootsMPol(res);
end intrinsic;

intrinsic MinValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the minimal valuation of f at roots of g}
	R := BaseRing(Parent(f));
	E<e> := PolynomialRing(R);
	T<t> := PolynomialRing(E);
	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));
	return MinValuationOfRootsMPol(res, p);
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

	//vs := [v[1] : v in ValuationsInRootsOf(Derivative(f)^k * g^(k-1), f) | v[1] ne Infinity()];
	//M := Max(M, Sup(vs));

	/*S<s> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	F := Evaluate(f, t)^k - s * Evaluate(g, t);
	disc := LeadingCoefficient(F) * Discriminant(F);
	d := Degree(F) - Degree(f);
	c := Coefficient(disc, d);

	v := Valuation(Coefficient(disc, d));
	for i := d + 1 to Degree(disc) do
		M := Max(M, (Valuation(Coefficient(disc, i)) - v) / (d - i));
	end for;*/

	return M;
end intrinsic;

intrinsic BoundPower(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := Max(0, k * Separant(f, p));
	M := Max(M, k * Separant(f, g, p));
	
	vs := [v[1] : v in ValuationsInRootsOf(Derivative(f)^k * g^(k-1), f, p) | v[1] ne Infinity()];
	M := Max(M, Sup(vs));

	/*S<s> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	F := Evaluate(f, t)^k - s * Evaluate(g, t);
	disc := LeadingCoefficient(F) * Discriminant(F);
	d := Degree(F) - Degree(f);
	c := Coefficient(disc, d);

	v := Valuation(Coefficient(disc, d), p);
	for i := d + 1 to Degree(disc) do
		M := Max(M, (Valuation(Coefficient(disc, i), p) - v) / (d - i));
	end for;*/

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
	F /:= lc;
	while exists {cs : cs in Coefficients(ct), ct in Coefficients(F) | Valuation(cs,p) lt 0} do
		F := p^Degree(F) * Evaluate(F, t/p);
	end while;

	printf "computing general separant\n";
	gen_sep := SeparantUPol(F) div t^Degree(F);

	printf "computing discriminant\n";
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
		d,cs := XGCD(f_hats);

		//assert Valuation(d - 1, p) ge Precision;
		//assert Valuation(unit - 1, p) ge Precision;

		//TODO: assert d = 1 and unit = 1 or something else.
		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in Zip(cs, fs)];

		// Construction of the Fi = fi^ki + s*ri
		Fis := [Evaluate(fr[1][1]^fr[1][2], tK) + sK * Evaluate(fr[2], tK) : fr in Zip(fs, rs)];

		// Translate the variable s in gen_sep by r
		sepK_r := SwitchVariables(Evaluate(SwitchVariables(gen_sep), tK + r));
		// Translate the variable s in FK by r
		FK_r := SwitchVariables(Evaluate(SwitchVariables(FK), tK + r));

		sepOKp_r := ROKp![Evaluate(ChangeRing(c, OKp), SOKp.1 + OKp!r) : c in Coefficients(gen_sep)];
		v_sep, b_sep := MaxValuationOfRootsMPol(sepOKp_r);
		printf "max sep: %o\n", v_sep;

		// The valuation of difference between FK_r and &*Fis is >= 2v(s) - min_val
		dif := FK_r - &*Fis;
		min_val := Min([Valuation(cs) : cs in Coefficients(ct), ct in Coefficients(dif)]);
		L<x> := PolynomialRing(Q);
		v_diff := 2*x + min_val;
		printf "min diff: %o\n", v_diff;

		min_val := Min([Valuation(cs) : cs in Coefficients(ct), ct in Coefficients(&*Fis)]);
		//TODO: bug? crash if not casted to ROKp
		v_deriv, b_deriv := MaxValuationInRootsOf(ROKp!Derivative(FK_r), ROKp!(pi^(-min_val) * &*Fis));
		printf "max deriv: %o\n", v_deriv;

		v_diff_roots, b_diff_roots := MaxValuationDiffRoots(ROKp!FK_r);
		printf "max diff_roots: %o\n", v_diff_roots;

		// When is diff > sep?
		assert (LeadingCoefficient(v_diff) gt LeadingCoefficient(v_sep));
		b1 := Floor(Roots(v_diff - v_sep)[1][1] + 1);
		printf "diff > sep if v(s) >= %o\n", b1;

		// When is deriv + diff_roots >= diff?
		assert (LeadingCoefficient(v_diff) gt LeadingCoefficient(v_deriv + v_diff_roots));
		b2 := Floor(Roots(v_diff - v_deriv - v_diff_roots)[1][1] + 1);
		printf "deriv + diff_roots >= diff if v(s) >= %o\n", b2;

		b_power := -Infinity();
		for fr in Zip(fs, rs) do
			b_power := Max(b_power, BoundPower(fr[1][1], fr[2], fr[1][2]));
		end for;
		// Make into inclusive bound
		b_power := Floor(b_power + 1);
		printf "power bound: %o\n", b_power;

		b_straight := -Infinity();
		for Fi in Fis do
			_,b := ValuationOfRootsMPolStraight(ValuationsInRootsOfUPol(Derivative(ROKp!Fi), ROKp!Fi));
			b_straight := Max(b_straight, b);
		end for;
		printf "straight bound: %o\n", b_straight;

		bound := Max(Max(Max(Max(Max(Max(Max(0, b_sep), b_deriv), b_diff_roots), b1), b2), b_power), b_straight);
		printf "bound (%o): %o\n", r, bound;

		//TODO: bounds for individual factors

		Append(~Nbhds_disc, r + O(pi^bound));

		k := LCM([fi[2] : fi in fs]);
		printf "k = %o\n", k;
		v := k * Ceiling(bound / k);
		v_power := 2*Valuation(K!k) + 1;
		OKmOKk := quo<OK | pi^v_power>; // OK / (OK)^k
		// representatives for OK* / (OK*)^k would be sufficient here
		//TODO: something separate with 0 here...?
		Nbhds_oo cat:= [CreatePAdicNbhd(X, OKp!r, (K!c) * pi^(v + w), k) : c in OKmOKk, w in [0..k-1]];
	end for;

	printf "computing nbhds\n";

	//gen_sep2 := RK!SwitchVariables(gen_sep);
	gen_mu_s := RK!SwitchVariables(ValuationsInRootsOfUPol(Derivative(F), F));
	min_val_s := Min([Valuation(cs, p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	// Split up in neighborhoods
	Nbhds := [O(K!1)];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	repeat
		#Nbhds;
		Nbhds_new := [];
		for N in Nbhds do
			if exists { Nd : Nd in Nbhds_disc | Nd in N } then
				Nbhds_new cat:= Subdivide(N, AbsolutePrecision(N) + 1);
			else
				//vals := ValuationsOfRoots(Evaluate(gen_sep2, N));
				//mu := Sup([v[1] : v in vals]) - min_val_s;
				vals := ValuationsOfRoots(Evaluate(gen_mu_s, N));
				mu := 2 * Sup([v[1] : v in vals]) - min_val_s;

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

	//return Nbhds_end;

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [CreatePAdicNbhd(X, OKp!n, pi^AbsolutePrecision(n), 1) : n in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, Filter)];

	printf "computing etale algebras for %o nbhds\n", #Nbhds;
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

//TODO: broken
intrinsic MaxValuationOfRootsMPol(res::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{}
	R := Parent(res);
	e := R.1;
	s := R.2;

	i := 0;
	while exists { c : c in Coefficients(res, e) | not CorrectAux(UnivariatePolynomial(c), p) } do
		res := Evaluate(res, [e, p*s]);
		i +:= 1;
	end while;

	L<x> := PolynomialRing(Q);
	vals := [<c[1], ValuationUPol(UnivariatePolynomial(c[2]), p)> : c in Zip([0..Degree(res,e)], Coefficients(res, e)) | c[2] ne 0];
	slopes := [(vals[1][2] - v[2]) / (v[1] - vals[1][1]) : v in vals[2..#vals]];
	a := Max([Coefficient(c,1) : c in slopes]);
	b := Max([ConstantCoefficient(c) : c in slopes | Coefficient(c,1) eq a]);

	while exists { c : c in slopes | ConstantCoefficient(c) gt b } do
		slopes := [c + Coefficient(c,1) : c in slopes];
		b +:= a;
		i +:= 1;
	end while;

	return a*x+b, i;
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
{}
	if f eq 0 then
		return true;
	end if;

	t := Parent(f).1;
	f := f div (t^(Z!Valuation(f)));
	return forall {v : v in ValuationsOfRoots(f, p) | v[1] lt 0};
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
	while exists { c : c in Coefficients(res) | not CorrectAux(c) } do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;

	L<x> := PolynomialRing(Q);
	vals := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
	slopes := [(vals[1][2] - v[2]) / (v[1] - vals[1][1]) : v in vals[2..#vals]];
	a := Max([Coefficient(c,1) : c in slopes]);
	b := Max([ConstantCoefficient(c) : c in slopes | Coefficient(c,1) eq a]);

	while exists { c : c in slopes | ConstantCoefficient(c) gt b } do
		slopes := [c + Coefficient(c,1) : c in slopes];
		b +:= a;
		i +:= 1;
	end while;

	//TODO: check that this is correct
	return a*x+b - i*b, i;
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
	while exists { c : c in Coefficients(res) | not CorrectAux(c) } do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;

	L<x> := PolynomialRing(Q);
	vals := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
	slopes := [(v[2] - vals[#vals][2]) / (vals[#vals][1] - v[1]) : v in vals[1..#vals-1]];
	a := Min([Coefficient(c,1) : c in slopes]);
	b := Min([ConstantCoefficient(c) : c in slopes | Coefficient(c,1) eq a]);

	while exists { c : c in slopes | ConstantCoefficient(c) lt b } do
		slopes := [c + Coefficient(c,1) : c in slopes];
		b +:= a;
		i +:= 1;
	end while;

	//TODO: check that this is correct
	return a*x+b - i*b, i;
end intrinsic;

intrinsic ValuationOfRootsMPolStraight(res::RngUPolElt) -> RngUPolElt, RngIntElt
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
	while exists { c : c in Coefficients(res) | not CorrectAux(c) } do
		// Scale the variable s in res by p
		res := SwitchVariables(Evaluate(SwitchVariables(res), p*e));
		i +:= 1;
	end while;

	L<x> := PolynomialRing(Q);
	vals_max := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
	slopes_max := [(v[2] - vals_max[#vals_max][2]) / (vals_max[#vals_max][1] - v[1]) : v in vals_max[1..#vals_max-1]];
	a_max := Min([Coefficient(c,1) : c in slopes_max]);
	b_max := Min([ConstantCoefficient(c) : c in slopes_max | Coefficient(c,1) eq a_max]);

	vals_min := [<c[1], ValuationUPol(c[2])> : c in Zip([0..Degree(res)], Coefficients(res)) | c[2] ne 0];
	slopes_min := [(v[2] - vals_min[#vals_min][2]) / (vals_min[#vals_min][1] - v[1]) : v in vals_min[1..#vals_min-1]];
	a_min := Min([Coefficient(c,1) : c in slopes_min]);
	b_min := Min([ConstantCoefficient(c) : c in slopes_min | Coefficient(c,1) eq a_min]);

	while exists { c : c in slopes_max | ConstantCoefficient(c) lt b_max } or
		  exists { c : c in slopes_min | ConstantCoefficient(c) lt b_min } or 
		  b_max ne b_max do
		slopes_max := [c + Coefficient(c,1) : c in slopes_max];
		slopes_min := [c + Coefficient(c,1) : c in slopes_min];
		b_max +:= a_max;
		b_min +:= a_min;
		i +:= 1;
	end while;

	//TODO: check that this is correct
	return a_max*x+b_max - i*b_max, i;
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
