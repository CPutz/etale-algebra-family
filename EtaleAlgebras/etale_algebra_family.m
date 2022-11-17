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

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	return Max([x[1] : x in ValuationsOfRoots(ValuationsInRootsOfUPol(f,g))]);
end intrinsic;

intrinsic MaxValuationInRootsOf(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngUPolElt, RngIntElt
{Returns the maximal valuation of f at roots of g}
	return Max([x[1] : x in ValuationsOfRoots(ValuationsInRootsOfUPol(f,g), p)]);
end intrinsic;

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngIntElt, .
{Bound on the valuation of s from [1,Theorem 32]  for which f^k - sg is structurally stable
together with the constant c from [1,Proposition 24]}
	R := Parent(f);
	K := BaseRing(R);
	_<s> := PolynomialRing(R);
	F := SwitchVariables(f^k - s*g);
	disc := Discriminant(F);
	F0 := LeadingCoefficient(F);
	c := Coefficient(F0 * disc, Degree(F) - Degree(f));
	df := Derivative(f);

	sigf := Separant(f);
	sigfg := Separant(f,g);
	//this bound is slightly worse than the real bound but easier to compute
	b := k * Valuation(K!k) + k * MaxValuationInRootsOf(df * g, f);
	vc := Valuation(c);
	b_mu := k * MaxValuationInRootsOf(df,f) + vc / Degree(f);

	"sigf", sigf;
	"sigfg", sigfg;
	"b", b;
	"vc", vc;
	"b_mu", b_mu;

	return Max([k*sigf, k*sigfg, b, vc, b_mu]), c;
end intrinsic;

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::PlcNumElt) -> RngIntElt, .
{Bound on the valuation of s from [1,Theorem 32]  for which f^k - sg is structurally stable
together with the constant c from [1,Proposition 24]}
	R := Parent(f);
	K := BaseRing(R);
	_<s> := PolynomialRing(R);
	F := SwitchVariables(f^k - s*g);
	disc := Discriminant(F);
	F0 := LeadingCoefficient(F);
	c := Coefficient(F0 * disc, Degree(F) - Degree(f));
	df := Derivative(f);

	sigf := Separant(f,p);
	sigfg := Separant(f,g,p);
	//this bound is slightly worse than the real bound but easier to compute
	b := k * Valuation(K!k,p) + k * MaxValuationInRootsOf(df * g, f, p);
	vc := Valuation(c,p);
	b_mu := k * MaxValuationInRootsOf(df,f,p) + vc / Degree(f);

	return Max([k*sigf, k*sigfg, b, vc, b_mu]), c;
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngUPolElt[RngUPol[FldRat]], p::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0,
	  MinVal := 0,
	  Hint := []) -> SeqEnum
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
		: D := D, Precision := Precision, Filter := Filter, MinVal := MinVal, Hint := Hint);
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngUPolElt, p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Precision := 500,
	  Filter := Integers(1)!0,
	  MinVal := 0,
	  Hint := []) -> SeqEnum
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
	OKpq := quo<OKp | piKp^Precision>;
	piOKpq := OKpq!piKp;
	X := pAdicNbhds(OKpq);

	//TODO: make monic and integral
	lc := LeadingCoefficient(LeadingCoefficient(F));
	vlc := Valuation(lc, p);
	F *:= pi^(-vlc);
	while exists {cs : cs in Coefficients(ct), ct in Coefficients(F) | Valuation(cs, p) lt 0} do
		F := pi^Degree(F) * Evaluate(F, t/pi);
	end while;

	vprintf EtaleAlg: "computing discriminant\n";
	disc := Discriminant(F);
	rootsK  := [r : r in Roots(disc, K) | Valuation(r[1],p) ge MinVal];
	//We assume that all integral roots of the discriminant over K_p are defined over K
	disc0 := disc div prod([(s - r[1])^r[2] : r in rootsK]);
	roots0Kp := [r[1] : r in Roots(StoSp(disc0),Kp) | Valuation(r[1]) ge MinVal];
	require IsEmpty(roots0Kp): "The integral roots of the discriminant over K_p should be defined over K";
	
	Nbhds_disc := []; // The neighborhoods around the roots of the discriminant
	Nbhds_oo := [];

	for r in rootsK do
		// Evaluate F at s = r
		f := StoSp(Evaluate(SwitchVariables(F), r[1]));
		// The coefficient of s in F
		g := StoSp(Coefficient(SwitchVariables(F), 1));

		fac := Factorization(f);
		fs := [<fi[1],fi[2]> : fi in fac];
		//f_hats := [f div fi[1]^fi[2] : fi in fs];
		if #fs eq 1 then
			f_hats := [f div fi[1]^fi[2] : fi in fs];
		else
			f_hats := [&*[fs[i,1] ^ fs[i,2] : i in [1..#fs] | i ne j] : j in [1..#fs]];
		end if;

		c,cs := XGCD(f_hats);

		/*if #fs eq 3 then
			c1,cs11,cs12 := XGCD(fs[1,1]^fs[1,2],fs[2,1]^fs[2,2]);
			c2,cs21,cs22 := XGCD(fs[1,1]^fs[1,2] * fs[2,1]^fs[2,2], c1*fs[3,1]^fs[3,2]);
			c := c2;
			cs := [cs12 * cs22, cs11 * cs22, cs21]; 

			"should be 1:",cs21 * f_hats[3] + cs22 * cs11 * f_hats[2] + cs22 * cs12 * f_hats[1]; 
		end if;*/

		min_val_ci := Min([Valuation(ci) : ci in Coefficients(c), c in cs] cat [0]);
		c := c * phi(pi)^(-min_val_ci);
		cs := [phi(pi)^(-min_val_ci) * c : c in cs];

		//assert that sum_i cs[i] * f_hats[i] = c
		assert forall {co : co in Coefficients(c - &+[fc[1]*fc[2] : fc in zip(cs, f_hats)]) | OKpq!co eq 0};
		
		assert Degree(c) eq 0;
		c := ConstantCoefficient(c);

		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in zip(cs, fs)];

		//TODO: can use min_val here to reduce bound by a lot
		bound := 0;
		ROKpq := PolynomialRing(OKpq);
		// Theorem 34
		for i := 1 to #fs do
			fi := fs[i][1];
			ki := fs[i][2];
			ri := rs[i];
			Fi := SwitchVariables(fi^ki - RtoRp(t)*ri);
			//TODO: these discriminant and separant computations crash magma if Fi is not exact (i.e. in ROKpq)
			stabi,ci := StabilityBound(ROKpq!fi, ROKpq!ri, ki);
			bi := Valuation(ci) / (Degree(fi)*ki);
			nu_i := MaxValuationInRootsOf(f_hats[i], fs[i,1]);
			boundi := Max(stabi, ki * (Valuation(c) + bi + nu_i));
			"boundi", boundi;
			"stabi", stabi;
			"bi", bi;
			"vc", Valuation(c);
			bound := Max(bound, boundi);
		end for;

		for i := 1 to #fs do
			for j := 1 to #fs do
				if i ne j then
					fi := fs[i][1];
					fj := fs[j][1];
					mu_ij := MaxValuationInRootsOf(fj, fi);
					"mu_ij", mu_ij;
					kj := fs[j][2];
					bound := Max(bound, 2 * Valuation(c) + kj * mu_ij);
				end if;
			end for;
		end for;

		vprintf EtaleAlg: "bound = %o\n", bound;
		bound := Ceiling(bound) + 1;

		Append(~Nbhds_disc, phi(r[1]) + O(piKp^bound));

		k := LCM([fi[2] : fi in fs]);
		vprintf EtaleAlg: "k = %o\n", k;
		v := k * Ceiling(bound / k);
		//v_power := 2*Valuation(K!k, p) + 1;
		//OKmOKk := quo<OKp | piKp^v_power>; // OK / (OK)^k

		//the group K*/(K*)^k
		KmKk,phik := pSelmerGroup(k,Kp);
		//TODO: something separate with 0 here...?
		Nbhds_oo cat:= [CreatePAdicNbhd(X, OKpq!r[1], (OKpq!(a@@phik)) * piOKpq^v, k) : a in KmKk | (a@@phik) ne 0];
	end for;

	vprintf EtaleAlg: "computing nbhds\n";

	min_val_s := Min([Valuation(cs,p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	if Degree(K) eq 1 then // K = Q
		vprintf EtaleAlg: "computing general separant\n";
		//compute the separant over Q because it is faster
		KtoQ := Coercion(K, Q);
		SQ,StoSQ := ChangeRing(S, Q, KtoQ);
		RQ,RtoRQ := ChangeRing(R, SQ, StoSQ);
		gen_sep := SwitchVariables(SeparantUPol(RtoRQ(F)) div t^Degree(F));
	else
		vprintf EtaleAlg: "computing general mu-bound\n";
		//compute mu_F and the difference between the roots of F instead of
		//the separant because computing separants over a number field is too slow
		gen_sep := SwitchVariables(ValuationsInRootsOfUPol(Derivative(F), F));
		gen_sep;
		Re<e> := PolynomialRing(S);
		Rx<x> := PolynomialRing(Re);
		_<y> := PolynomialRing(Rx);
		vprintf EtaleAlg: "computing general difference of roots\n";
		dif := SwitchVariables(Resultant(Resultant(e - (x-y), Evaluate(F,y)), Evaluate(F,x)) div e^Degree(F));
	end if;
	

	// Subdivide in neighborhoods
	Nbhds := [<K!0,0>];
	Nbhds_end := [];  // The neighborhoods that do not contain a root of the discriminant
	depth := 0;
	repeat
		Nbhds_new := [];
		depth +:= 1;
		vprintf EtaleAlg: "subdivision %o with %o neighbourhoods\n", depth, #Nbhds;
		for N in Nbhds do
			Np := phi(N[1]) + O(piKp^N[2]);
			if exists { Nd : Nd in Nbhds_disc | Nd in Np } then
				Nbhds_new cat:= Subdivide(N[1], N[2], N[2] + 1, p);
			elif exists { Nd : Nd in Nbhds_disc | Np in Nd } then
				//Do nothing since N is contained in one of the neighborhoods around a root of the discriminant
			else
				sN := Evaluate(gen_sep, N[1]);
				dN := Evaluate(dif, N[1]);
				sig := Max([r[1] : r in ValuationsOfRoots(sN,Ideal(p))]) + Max([r[1] : r in ValuationsOfRoots(dN,Ideal(p))]);

				if sig - min_val_s lt N[2] then
					Append(~Nbhds_end, N);
				else
					Nbhds_new cat:= Subdivide(N[1], N[2], Floor(sig - min_val_s + 1), p);
				end if;
			end if;
		end for;
		Nbhds := Nbhds_new;

		// Filter
		//"#Nbhds before:", #Nbhds;
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(CreatePAdicNbhd(X, OKpq!phi(N[1]), piOKpq^N[2], 1), Filter, MinVal)];
		//"#Nbhds after:", #Nbhds;
	until IsEmpty(Nbhds);

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [CreatePAdicNbhd(X, OKpq!phi(N[1]), piOKpq^N[2], 1) : N in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, Filter, MinVal)];

	vprintf EtaleAlg: "computing etale algebras for %o nbhds\n", #Nbhds;
	//use finite precision for last step
	KpP := ChangePrecision(Kp, Precision);
	psi := Coercion(Kp, KpP);
	SpP,StoSpP := ChangeRing(S, KpP, phi * psi);
	RpP,RtoRpP := ChangeRing(R, SpP, StoSpP);

	//make sure we do not choose a zero of the discriminant as a representative for a neighbourhood
	//assert forall {N : N in Nbhds | Valuation(x) lt AbsolutePrecision(x) where x := Evaluate(StoSpP(disc), Representative(N))};

	//E := EtaleAlgebraListIsomorphism2(RtoRpP(F), Nbhds : D := D);
	E := FindIsomorphismClasses([Evaluate(SwitchVariables(RtoRpP(F)),Representative(N)) : N in Nbhds] :
		D := D, Data := Nbhds, Hint := Hint);

	return E;
end intrinsic;



/*intrinsic Subdivide(x::FldPadElt, n::RngIntElt) -> SeqEnum
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
end intrinsic;*/

intrinsic Subdivide(x::FldNumElt, r::RngIntElt, n::RngIntElt, p::PlcNumElt) -> SeqEnum
{}
	if n le r then
		return [x];
	else
		K := Parent(x);
		OK := Integers(K);
		pi := UniformizingElement(p);

		Kp,KtoKp := Completion(K,p);
		OKp := Integers(Kp);
		pip := UniformizingElement(Kp);

		//R := quo<OK | pi^(n - r)>;
		R := quo<OKp | pip^(n - r)>;
		phi := Coercion(OKp, R);
		S := quo<OK | pi^n>;

		return SetToSequence({<K!(OK!S!x + pi^r * (y@@phi)@@KtoKp), n> : y in R});
	end if;
end intrinsic;

//TODO: Make obsolete
intrinsic 'in'(x::FldPadElt, y::FldPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;

intrinsic 'in'(x::RngPadElt, y::RngPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;