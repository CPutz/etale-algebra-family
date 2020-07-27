Z := Integers();
Q := Rationals();
EtRF := recformat< E : EtAlg, B0 : SeqEnum, Boo : SeqEnum >;

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

	vs := [v[1] : v in ValuationsInRootsOf(Derivative(f)^k * g^(k-1), f) | v[1] ne Infinity()];
	M := Max(M, Sup(vs));

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

intrinsic EtaleAlgebraFamily2(F::RngUPolElt, p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500) -> .
{}
	R := Parent(F); //Z[s][t] or Q[s][t]
	S := BaseRing(R); //Z[s] or Q[s]
	require ISA(Type(BaseRing(S)), RngInt) or ISA(Type(BaseRing(S)), FldRat):
		"Argument 1 must be defined over Z or Q";

	s := S.1;
	t := R.1;
	K := pAdicField(p, Precision);
	OK := Integers(K);
	X := pAdicNbhds(K);
	pi := K!p;

	//TODO: make monic and integral
	lc := LeadingCoefficient(LeadingCoefficient(F));
	F /:= lc;

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
	Nbhds_oo := [];

	for r in roots do	
		// Evaluate F at s = r
		f := Evaluate(SwitchVariables(FK), r);
		// The coefficient of s in F
		g := Coefficient(SwitchVariables(FK), 1);

		fs,unit := Factorization(f);
		f_hats := [f div fi[1]^fi[2] : fi in fs];
		d,cs := XGCD(f_hats);

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
		if min_val gt 0 then
			min_val := 0;
		end if;
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

		bound := Max(Max(Max(Max(b_sep, b_deriv), b_diff_roots), b1), b2);
		printf "bound (%o): %o\n", r, bound;

		Append(~Nbhds_oo, r + O(pi^bound));

		//TODO: split up the Nbhds_oo
	end for;

	gen_sep2 := RK![ChangeRing(c, K) : c in Coefficients(SwitchVariables(gen_sep))];
	// Split up in neighborhoods
	Nbhds := [O(K!1)];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	i := 0;
	repeat
		i;
		Nbhds_new := [];
		for N in Nbhds do
			vals := ValuationsOfRoots(Evaluate(gen_sep2, N));
			sep := Sup([v[1] : v in vals]);

			if sep lt AbsolutePrecision(N) then
				Append(~Nbhds_end, N);
			elif exists { Noo : Noo in Nbhds_oo | N in Noo } then
				//Do nothing, N is contained in one of the limit neighborhoods
			elif sep lt Infinity() then
				Nbhds_new cat:= Subdivide(N, Floor(sep + 1));
			else
				Nbhds_new cat:= Subdivide(N, AbsolutePrecision(N) + 1);
			end if;
		end for;
		Nbhds := Nbhds_new;
		i +:= 1;
	until IsEmpty(Nbhds);

	return Nbhds_end, Nbhds_oo;
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

	return a*x+b, i;
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

	return a*x+b, i;
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
{}
	if f eq 0 then
		return true;
	end if;

	t := Parent(f).1;
	f := f div (t^(Z!Valuation(f)));
	return forall {v : v in ValuationsOfRoots(f) | v[1] lt 0};
end intrinsic;



intrinsic EtaleAlgebraFamily(F::RngMPolElt, p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500) -> .
{}
	require ISA(Type(BaseRing(Parent(F))), RngInt) or ISA(Type(BaseRing(Parent(F))), FldRat):
		"Argument 1 must be defined over Z or Q";

	R := Parent(F);
	s := R.1;
	t := R.2;
	K := pAdicField(p, Precision);
	OK := Integers(K);
	X := pAdicNbhds(K);
	pi := K!p;

	//TODO: make monic and integral

	// Compute discriminant and find roots
	disc := UnivariatePolynomial(Discriminant(F, 2));
	roots_Zp := [x[1] : x in Roots(disc, K) | IsIntegral(x[1])];

	// Split up in neighborhoods
	OKp := quo<OK | p^Precision>;
	C := [OKp!0];
	C0 := [];  // The neighborhoods that do not contain a root of the discriminant
	Coo := []; // The neighborhoods that do     contain a root of the discriminant
	i := 0;
	repeat
		C_new := [];
		for c in C do
			// Count the number of roots of the discriminant in the neighborhood c
			number_roots_in_c := #{ r : r in roots_Zp | r in (K!c + O(pi^i)) };
			if number_roots_in_c eq 0 then
				Append(~C0, K!c + O(p^i));
			elif number_roots_in_c eq 1 then
				Append(~Coo, CreatePAdicNbhd(X, c, pi^i, 1));
			else
				C_new cat:= [ c + (OKp!pi)^i * OKp!x : x in ResidueSystem(K) ];
			end if;
		end for;
		C := C_new;
		i +:= 1;
	until IsEmpty(C);

	for c in Coo do
		c0 := Middle(c);
		pe := Radius(c);
		// Find the root of the discriminant r0 which lies inside c
		assert exists (r0) { r : r in [ro : ro in roots_Zp] | r in (K!c0 + O(K!pe)) };

		printf "computing around singular point: %o\n", r0;
		//F0 := Evaluate(F, [r0 + pe * s, t]);
		// Make monic and integral
		//F0 := F0 / Coefficient(F0, t, Degree(F0, t)); //make monic in t
		Fp := ChangeRing(F, K);
		Rp := Parent(Fp);
		sp := Rp.1;
		tp := Rp.2;
		f := UnivariatePolynomial(Evaluate(Fp, [r0, tp]));
		g := UnivariatePolynomial(Coefficient(Evaluate(Fp, [r0 + pe * sp, tp]), sp, 1)); //TODO: deal with higher powers of s 
		Factorization(f);
		g;

		fac,_ := Factorization(f);
		fs := [fi[1] : fi in fac];
		fs_hat := [f div (fi[1]^fi[2]) : fi in fac];
		d,cs := XGCD(fs_hat);

		assert Degree(d) eq 0;
		d := ConstantCoefficient(d);

		min_val := Min([Valuation(c) : c in Coefficients(ci), ci in cs]);
		content := pi^(-min_val);
		// Rescale the ci and d
		cs := [content * c : c in cs];
		d *:= content;

		d;
		cs;

		rs := [(cf[1] * g) mod cf[2] : cf in Zip(cs, fs)];

		nus := [v[1] : v in ValuationsInRootsOf(fhi[1], fhi[2]), fhi in Zip(fs_hat, fs)];
		mus := [fj[2] * v[1] : v in ValuationsInRootsOf(fj[1], fi), fi in fs, fj in fac | fi ne fj[1]];

		//TODO: compute the bi's
		bs := [0 : f in fs];

		bound1 := Sup([fac[i][2] * (Valuation(d) + bs[i] + nus[i]) : i in [1..#fac]]);
		bound2 := Sup([Valuation(d) + mu : mu in mus]);

		//bound for the fi^ki - sri
		bound := Max(bound1, bound2);

		bound;

		/*
		//require Degree(F0, s) le 1: "Degree of g in s must be <= 1.";
		g := -UnivariatePolynomial(Coefficient(F0, s, 1));
		Facf := Factorization(f);
		facs := [fac[1]^fac[2] : fac in Facf];
		_, cs := Xgcd([f div h : h in facs]);
		fcs := Zip(facs, cs);
		rs := [(fc[2] * g) mod fc[1] : fc in fcs];

		bound := 0;
		k := 1;
		for i := 1 to #Facf do
			ki := Facf[i][2];
			bound := Max(bound, EtaleAlgebraFamily0Bound(Facf[i][1], rs[i], ki));
			k := Lcm(k, ki);
		end for;
		printf "using bound %o\n", bound;

		printf "computing separant\n";
		if FZ eq 0 then
			F1 := UnivariatePolynomial(Evaluate(F0, s, p));
			sig1 := Separant(F1);
		else
			FZ1 := UnivariatePolynomial(Evaluate(FZ, 1, Prime(K)));
			sig1 := Separant(FZ1, Prime(K));
		end if;

		vg := Valuation(Content(ChangeRing(g, OK)));
		prec := Max(0, Floor(sig1 - 1 - vg) + 1);

		printf "generating p-adic neighbourhoods\n";
		//TODO: prove that linearly extending the separant works
		B := [];
		for i := 1 to bound - 1 do
			B cat:= [X!(p^i * c + O(p^(prec+i))) : c in quo<OK | (OK!p)^prec> | Valuation(c) eq 0];
		end for;

		//TODO: change
		Precision := 500;
		OKp := quo<OK | p^Precision>;
		for i := 0 to k-1 do
			B cat:= [CreatePAdicNbhd(X, OKp!0, p^(bound+i) * K!c, k) : c in RepresentativesModuloPower(OK, k)];
		end for;

		//transform back
		B := [r0 + pe * X!b : b in B];
		C_end cat:= B;*/
	end for;

	// Compute the general separant of F
	sep := SeparantMPol(F, t) / t^Degree(F,t);

	//
	for c in C0 do
		sep_c := Sup([x[1] : x in ValuationsOfRoots(UnivariatePolynomial(Evaluate(sep, s, c)))]);
		c;
		sep_c;
	end for;

	return 0;
end intrinsic;
/*
intrinsic EtaleAlgebraFamily(F::RngMPolElt, v::RngIntResElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  FZ := 0) -> .
{}
	P := Parent(F);
	s := P.1;
	t := P.2;
	K := BaseRing(P);
	OK := Integers(K);
	X := pAdicNbhds(K);
	p := UniformizingElement(K);
	require ISA(Type(K), FldPad): "Argument 1 must be a polynomial over a p-adic field";
	require Rank(P) eq 2: "Argument 1 must be a polynomial in 2 variables";

	printf "computing general discriminant\n";
	disc := UnivariatePolynomial(Discriminant(F, 2));
	roots_Zp := [r[1] : r in Roots(disc) | Valuation(r[1]) ge 0];
	Roots(disc);

	
	//TODO: change
	OKp := quo<OK | p^Precision>;

	C := [OKp!0];
	C_end := [];
	C0 := [];
	i := 0;
	repeat
		C_new := [];
		for c in C do
			//if not HasRoot(Evaluate(disc, cp + p^i * Parent(disc).1))then
			n_roots_in_c := #{ r : r in roots_Zp | r in (K!c + O(p^i)) };
			if n_roots_in_c eq 0 then
				C_end cat:= [ X!(K!c + x*p^i) : x in ResidueSystem(K) ];
			elif n_roots_in_c eq 1 then
				Append(~C0, CreatePAdicNbhd(X, c, p^i, 1));
			else
				C_new cat:= [ c + (OKp!p)^i * OKp!x : x in ResidueSystem(K) ];
			end if;
		end for;
		C := C_new;
		i +:= 1;
	until IsEmpty(C);

	for c in C0 do
		c0 := Middle(c);
		pe := Radius(c);
		assert exists (r0) { r : r in [ro : ro in roots_Zp] | r in (K!c0 + O(K!pe)) };

		printf "computing around singular point: %o\n", r0;
		//TODO: do not cast r0 to Z!
		F0 := Evaluate(F, [Z!r0 + pe * s, t]);
		//F0 := F0 / Coefficient(F0, t, Degree(F0, t)); //make monic in t
		//TODO: do not cast r0 to Z!
		f := UnivariatePolynomial(Evaluate(F, [Z!r0, t]));

		//require Degree(F0, s) le 1: "Degree of g in s must be <= 1.";
		g := -UnivariatePolynomial(Coefficient(F0, s, 1));
		Facf := Factorization(f);
		facs := [fac[1]^fac[2] : fac in Facf];
		_, cs := Xgcd([f div h : h in facs]);
		fcs := Zip(facs, cs);
		rs := [(fc[2] * g) mod fc[1] : fc in fcs];

		bound := 0;
		k := 1;
		for i := 1 to #Facf do
			ki := Facf[i][2];
			bound := Max(bound, EtaleAlgebraFamily0Bound(Facf[i][1], rs[i], ki));
			k := Lcm(k, ki);
		end for;
		printf "using bound %o\n", bound;

		printf "computing separant\n";
		if FZ eq 0 then
			F1 := UnivariatePolynomial(Evaluate(F0, s, p));
			sig1 := Separant(F1);
		else
			FZ1 := UnivariatePolynomial(Evaluate(FZ, 1, Prime(K)));
			sig1 := Separant(FZ1, Prime(K));
		end if;

		vg := Valuation(Content(ChangeRing(g, OK)));
		prec := Max(0, Floor(sig1 - 1 - vg) + 1);

		printf "generating p-adic neighbourhoods\n";
		//TODO: prove that linearly extending the separant works
		B := [];
		for i := 1 to bound - 1 do
			B cat:= [X!(p^i * c + O(p^(prec+i))) : c in quo<OK | (OK!p)^prec> | Valuation(c) eq 0];
		end for;

		//TODO: change
		Precision := 500;
		OKp := quo<OK | p^Precision>;
		for i := 0 to k-1 do
			B cat:= [CreatePAdicNbhd(X, OKp!0, p^(bound+i) * K!c, k) : c in RepresentativesModuloPower(OK, k)];
		end for;

		//transform back
		B := [r0 + pe * X!b : b in B];
		C_end cat:= B;
	end for;

	//filter C_end
	C_end := [N : N in C_end | ContainsElementOfValuation(N, v)];
	printf "computing étale algebras for %o polynomials\n", #C_end;
	E := EtaleAlgebraListIsomorphism2(F, C_end : D := D);
	for i := 1 to #E do
		E[i][2] := GeneralizeNbhds(E[i][2]);
	end for;

	return E;
end intrinsic;


intrinsic EtaleAlgebraFamily0Bound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngIntElt
{}
	require Degree(g) le k * Degree(f): "Degree of f^k must be at least the degree of g";
	K := CoefficientRing(f);
	OK := Integers(K);
	X := pAdicNbhds(K);
	require Parent(f) eq Parent(g): "Argument 1 and 2 must be defined over the same field";
	require ISA(Type(K), FldPad): "Argument 1 and 2 must be defined over a p-adic field";
	//require Valuation(LeadingCoefficient(f)) eq 0: "Argument 1 must be monic (the leading coefficient must be a unit)";
	f /:= LeadingCoefficient(f);
	g /:= LeadingCoefficient(f);

	//Scale polynomials to be monic and have integral coefficients
	P := Parent(f);
	p := UniformizingElement(K);
	while exists { c : c in Coefficients(g) | Valuation(c) lt 0 } do
		f := p^Degree(f) * Evaluate(f, P.1 / p);
		g := p^(Degree(f) * k) * Evaluate(g, P.1 / p);
	end while;

	R<s,t> := PolynomialRing(K, 2);
	phi := hom<Parent(f) -> R | Parent(f).1 -> t>;
	F := phi(f)^k - s * phi(g);
	disc := UnivariatePolynomial(Discriminant(F, t));

	v0 := &+([0] cat [r[2] : r in Roots(disc) | Valuation(r[1]) ge 0]);
	require v0 eq Degree(f) * (k - 1): "F(s,t) may only have s = 0 as a singular point in Zp";

	bound := Ceiling(Bound1(f, g, k));
	printf "bound: %o\n", bound;

	return bound;
end intrinsic;

FactorizationStructureList := function(L)
    return Sort([<Degree(Ki[1]), Ki[2]> : Ki in L]);
end function;

intrinsic EtaleAlgebraListIsomorphism2(F::RngMPolElt, B::SeqEnum :
	D := LocalFieldDatabase()) -> SeqEnum[Tup]
{Creates a list of etale algebra given a polynomial F in 2 variables over a local field
and a list B of parameter values}
    if IsEmpty(B) then
        return [];
    end if;

    Res := [];
    //K := Parent(B[1]); 
    OK := ISA(Type(Universe(B)), PadNbhd) select AmbientSpace(Parent(B[1])) else RingOfIntegers(Parent(B[1]));
    R := PolynomialRing(OK);

    P := Parent(F);

    factorizations := [<Factorization(R ! MakeMonicIntegral(UnivariatePolynomial(Evaluate(F, [Representative(s), P.2])))),
    	UnivariatePolynomial(Evaluate(F, [Representative(s), P.2])), s> : s in B];
    Fstructures := {@ FactorizationStructureList(fac[1]) : fac in factorizations @};
    Fstructures;
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



intrinsic Splits(f::RngUPolElt, R::Rng) -> BoolElt
{Returns whether f splits over the ring R.}
	return &+([0] cat [r[2] : r in Roots(f, R)]) eq Degree(f);
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
*/

intrinsic 'in'(x::FldPadElt, y::FldPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;

intrinsic 'in'(x::RngPadElt, y::RngPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;
