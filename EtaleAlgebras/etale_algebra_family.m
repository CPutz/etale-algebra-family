declare verbose EtaleAlg, 1;

import "utils.m" : zip, sup, prod;

Z := Integers();
Q := Rationals();

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



/*intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
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
*/

intrinsic BoundPower(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := Max(0, k * Separant(f));
	M := Max(M, k * Separant(f, g));
	M := Max(M, k * Separant(f, Derivative(g)));

	vs := [v[1] : v in ValuationsInRootsOfQuotient(Derivative(f)^k * g^(k-1), Derivative(g)^k, f) | v[1] ne Infinity()];
	M := Max(M, sup(vs));

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
	M := Max(M, sup(vs));

	//for i := 0 to k*Degree(f) do
	//	M := Max(M, Valuation(Coefficient(f^k, i), p) - Valuation(Coefficient(g, i), p));
	//end for;

	return M;
end intrinsic;


intrinsic EtaleAlgebraFamily(F::RngUPolElt[RngUPol[FldRat]], p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0) -> SeqEnum
{}
	R := Parent(F);
	S := BaseRing(R);
	Q := BaseRing(S);

	Qnf := RationalsAsNumberField();
	QtoQnf := Coercion(Q, Qnf);
	Snf,StoSnf := ChangeRing(S, Qnf, QtoQnf);
	Rnf,RtoRnf := ChangeRing(R, Snf, StoSnf);

	pl := Decomposition(Qnf, p)[1,1];

	return EtaleAlgebraFamily(RtoRnf(F), pl
		: D := D, Precision := Precision, Filter := Filter);
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngUPolElt, p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0) -> SeqEnum
{}
	R := Parent(F);
	S := BaseRing(R);
	t := R.1;
	s := S.1;

	K := BaseRing(S);
	OK := Integers(K);
	pi := UniformizingElement(p);

	Kp,phi := Completion(K,p : Precision := Precision);
	OKp := Integers(Kp);
	piKp := UniformizingElement(Kp);
	Sp,StoSp := ChangeRing(S, Kp, phi);
	Rp,RtoRp := ChangeRing(R, Sp, StoSp);

	//TODO: make monic and integral
	lc := LeadingCoefficient(LeadingCoefficient(F));
	F /:= lc;
	while exists {cs : cs in Coefficients(ct), ct in Coefficients(F) | Valuation(cs, p) lt 0} do
		F := pi^Degree(F) * Evaluate(F, t/pi);
	end while;

	vprintf EtaleAlg: "computing discriminant\n";
	disc := Discriminant(F);
	vd0 := Valuation(LeadingCoefficient(disc), p);
	rootsK  := [r : r in Roots(disc, K) | Valuation(r[1],p) ge 0];
	//We assume that all integral roots of the discriminant over K_p are defined over K
	disc0 := disc div prod([(s - r[1])^r[2] : r in rootsK]);
	roots0Kp := [r[1] : r in Roots(StoSp(disc0),Kp) | Valuation(r[1]) ge 0];
	require IsEmpty(roots0Kp): "The integral roots of the discriminant over K_p should be defined over K";

	KpP := ChangePrecision(Kp, Precision);
	psi := Coercion(Kp, KpP);
	OKP := Integers(KpP);
	piKpP := KpP!phi(pi);
	OKpq := quo<OKP | piKpP^Precision>;
	X := pAdicNbhds(KpP);
	Nbhds_disc := []; // The neighborhoods around the roots of the discriminant
	Nbhds_oo := [];

	for r in rootsK do
		// Evaluate F at s = r
		f := StoSp(Evaluate(SwitchVariables(F), r[1]));
		// The coefficient of s in F
		g := StoSp(Coefficient(SwitchVariables(F), 1));

		fac := Factorization(f);
		fs := [<fi[1],fi[2]> : fi in fac];
		f_hats := [f div fi[1]^fi[2] : fi in fs];

		c,cs := XGCD(f_hats);
		min_val := Min([Valuation(ci) : ci in Coefficients(c), c in cs] cat [0]);
		d := c * phi(pi)^min_val;
		cs := [phi(pi)^min_val * c : c in cs];

		//assert that sum_i cs[i] * f_hats[i] = d
		//assert forall {c : c in Coefficients(d - &+[fc[1]*fc[2] : fc in zip(cs, f_hats)]) | K!0 in c};
		
		//assert &+[fc[1]*fc[2] : fc in zip(cs, f_hats)] eq d;
		assert Degree(d) eq 0;
		d := ConstantCoefficient(d);
		//assert d eq 1;

		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in zip(cs, fs)];

		bound := 0;
		for i := 1 to #fs do
			fi := fs[i][1];
			ki := fs[i][2];
			ri := rs[i] / d;
			min_val_s := Min([Valuation(cs) : cs in Coefficients(ri)]);
			ri := ri / phi(pi)^min_val_s;
			Fi := SwitchVariables(fi^ki - RtoRp(t)*ri);
			//TODO: this discriminant and separant computations crash magma if Fi is not exact
			disci := Discriminant(PolynomialRing(PolynomialRing(OKpq))!Fi);
			ci := Valuation(ki * LeadingCoefficient(fi) * Coefficient(disci, Degree(Fi) - Degree(fi)));
			sigf := Separant(PolynomialRing(OKpq)!fi);
			sigfr := Separant(PolynomialRing(OKpq)!fi, PolynomialRing(OKpq)!ri);
			bi := StabilityBound(PolynomialRing(OKpq)!fi, PolynomialRing(OKpq)!ri, ki);
			boundi := Max([ki*sigf, ki*sigfr, bi, ci]) - min_val_s;

			bound := Max(bound, boundi);
		end for;
		vprintf EtaleAlg: "bound = %o\n", bound;
		bound := Ceiling(bound);

		Append(~Nbhds_disc, phi(r[1]) + O(piKp^bound));

		k := LCM([fi[2] : fi in fs]);
		vprintf EtaleAlg: "k = %o\n", k;
		v := k * Ceiling(bound / k);
		v_power := 2*Valuation(K!k, p) + 1;
		OKmOKk := quo<OKp | piKp^v_power>; // OK / (OK)^k
		// representatives for OK* / (OK*)^k would be sufficient here
		//TODO: something separate with 0 here...?
		Nbhds_oo cat:= [CreatePAdicNbhd(X, OKpq!r[1], (KpP!c) * piKpP^(v + w), k) : c in OKmOKk, w in [0..k-1]];
	end for;

	vprintf EtaleAlg: "computing nbhds\n";

	min_val_s := Min([Valuation(cs,p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	// Subdivide in neighborhoods
	Nbhds := [<K!0,0>];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	depth := 0;
	repeat
		Nbhds_new := [];
		vprintf EtaleAlg: "depth %o with %o nbhds\n", depth, #Nbhds;
		depth +:= 1;
		for N in Nbhds do
			Np := phi(N[1]) + O(piKp^N[2]);
			if exists { Nd : Nd in Nbhds_disc | Nd in Np } then
				Nbhds_new cat:= Subdivide(N[1], N[2], N[2] + 1, p);
			elif exists { Nd : Nd in Nbhds_disc | Np in Nd } then
				//Do nothing since N is contained in one of the neighborhoods around a root of the discriminant
			else
				FN := Evaluate(SwitchVariables(F), N[1]);
				sig := Separant(FN, p) - min_val_s;

				if sig lt N[2] then
					Append(~Nbhds_end, N);
				else
					Nbhds_new cat:= Subdivide(N[1], N[2], Floor(sig + 1), p);
				end if;
			end if;
		end for;
		Nbhds := Nbhds_new;
		//"#Nbhds before:", #Nbhds;
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(CreatePAdicNbhd(X, OKpq!N[1], piKpP^N[2], 1), Filter)];
		//"#Nbhds after:", #Nbhds;

		// Filter
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(CreatePAdicNbhd(X, OKpq!N[1], piKpP^N[2], 1), Filter)];
	until IsEmpty(Nbhds);

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [CreatePAdicNbhd(X, OKpq!N[1], piKpP^N[2], 1) : N in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, Filter)];

	vprintf EtaleAlg: "computing etale algebras for %o nbhds\n", #Nbhds;
	SpP,StoSpP := ChangeRing(S, KpP, phi * psi);
	RpP,RtoRpP := ChangeRing(R, SpP, StoSpP);

	//make sure we do not choose a zero of the discriminant as a representative for a neighbourhood
	assert forall {N : N in Nbhds | Valuation(x) lt AbsolutePrecision(x) where x := Evaluate(StoSpP(disc), Representative(N))};

	//E := EtaleAlgebraListIsomorphism2(RtoRpP(F), Nbhds : D := D);
	E := FindIsomorphismClasses([Evaluate(SwitchVariables(RtoRpP(F)),Representative(N)) : N in Nbhds] : D := D, Data := Nbhds);

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

		return SetToSequence({K!((S!x) + pi^r * y) : y in R});
	end if;
end intrinsic;

intrinsic Subdivide(x::FldNumElt, r::RngIntElt, n::RngIntElt, p::PlcNumElt) -> SeqEnum
{}
	if n le r then
		return [x];
	else
		K := Parent(x);
		OK := Integers(K);
		pi := UniformizingElement(p);
		R := quo<OK | pi^(n - r)>;
		S := quo<OK | pi^n>;

		return SetToSequence({<K!(OK!S!x + pi^r * OK!y), n> : y in R});
	end if;
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
