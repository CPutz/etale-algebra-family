/*
 * Isomorphism classes of families of etale algebras parametrized by one variable.
 */

declare verbose EtaleAlg, 1;

import "utils.m" : zip, prod;
Q := Rationals();

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngIntElt, RngElt
{Bound on the valuation of s for which f^k - sg is structurally stable
together with a constant c used in further computations.}
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

	return Max([k*sigf, k*sigfg, b, vc, b_mu]), c;
end intrinsic;

intrinsic StabilityBound(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::PlcNumElt) -> RngIntElt, RngElt
{Bound on the valuation of s for which f^k - sg is structurally stable
together with a constant c used in further computations.}
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
	  Hint := [],
	  Precision := 50,
	  CongrVal := Integers(1)!0,
	  MinVal := 0,
	  BoundMethod := "Default") -> SeqEnum
{For F in Q[s][t], computes all isomorphism classes of etale algebras over Q_p
generated by F when s is specialized to all value in OK_p for which F(s,t) is separable.
A database of local fields D can be provided for faster searching of the etale algebras
and a list of possible etale algebras to try first can be provided using the parameter Hint.
All computations will be performed with the provided Precision (default 50). As an
additional restriction, s can be restricted to have valuation >= MinVal using the
corresponding parameter, and if CongrVal is set the value of c in Z/mZ then only values of
s with v(s) = c (mod m) will be considered. The parameter BoundMethod decides which
bound for Hensels lemma is used during the computations (this can greatly improve
computation times). Options for BoundMethod are Default, Separant, Derivative and
Difference.}

	R := Parent(F);
	S := BaseRing(R);
	Q := BaseRing(S);

	Qnf := RationalsAsNumberField();
	QtoQnf := Coercion(Q, Qnf);
	Snf,StoSnf := ChangeRing(S, Qnf, QtoQnf);
	Rnf,RtoRnf := ChangeRing(R, Snf, StoSnf);

	pl := Decomposition(Qnf, p)[1,1];

	return EtaleAlgebraFamily(RtoRnf(F), pl
		: D := D, Precision := Precision, CongrVal := CongrVal, MinVal := MinVal,
			Hint := Hint, BoundMethod := BoundMethod);
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngUPolElt[RngUPol[FldNum]], p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Precision := 50,
	  CongrVal := Integers(1)!0,
	  MinVal := 0,
	  Hint := [],
	  BoundMethod := "Default") -> SeqEnum
{For F in K[s][t], computes all isomorphism classes of etale algebras over K_p
generated by F when s is specialized to all value in OK_p for which F(s,t) is separable.
A database of local fields D can be provided for faster searching of the etale algebras
and a list of possible etale algebras to try first can be provided using the parameter Hint.
All computations will be performed with the provided Precision (default 50). As an
additional restriction, s can be restricted to have valuation >= MinVal using the
corresponding parameter, and if CongrVal is set the value of c in Z/mZ then only values of
s with v(s) = c (mod m) will be considered. The parameter BoundMethod decides which
bound for Hensels lemma is used during the computations (this can greatly improve
computation times). Options for BoundMethod are Default, Separant, Derivative and
Difference.}

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

	// Make F monic and integral
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
		require g ne 0: "F must have a linear term in s";

		fac := Factorization(f);
		fs := [<fi[1],fi[2]> : fi in fac];
		//f_hats := [f div fi[1]^fi[2] : fi in fs];
		if #fs eq 1 then
			f_hats := [f div fi[1]^fi[2] : fi in fs];
		else
			f_hats := [&*[fs[i,1] ^ fs[i,2] : i in [1..#fs] | i ne j] : j in [1..#fs]];
		end if;

		c,cs := XGCD(f_hats);
		min_val_ci := Min([Valuation(ci) : ci in Coefficients(c), c in cs] cat [0]);
		c := c * phi(pi)^(-min_val_ci);
		cs := [phi(pi)^(-min_val_ci) * c : c in cs];

		//assert that sum_i cs[i] * f_hats[i] = c
		assert forall {co : co in Coefficients(c - &+[fc[1]*fc[2] : fc in zip(cs, f_hats)]) | OKpq!co eq 0};
		
		assert Degree(c) eq 0;
		c := ConstantCoefficient(c);

		rs := [(cf[1] * g) mod (cf[2][1]^cf[2][2]) : cf in zip(cs, fs)];

		bound := 0;
		ROKpq := PolynomialRing(OKpq);

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
			bound := Max(bound, boundi);
		end for;

		for i := 1 to #fs do
			for j := 1 to #fs do
				if i ne j then
					fi := fs[i][1];
					fj := fs[j][1];
					mu_ij := MaxValuationInRootsOf(fj, fi);
					kj := fs[j][2];
					bound := Max(bound, 2 * Valuation(c) + kj * mu_ij);
				end if;
			end for;
		end for;

		vprintf EtaleAlg: "bound = %o\n", bound;
		bound := Floor(bound + 1);

		Append(~Nbhds_disc, phi(r[1]) + O(piKp^bound));

		k := LCM([fi[2] : fi in fs]);
		vprintf EtaleAlg: "k = %o\n", k;
		v := k * Ceiling(bound / k);

		//the group K*/(K*)^k
		KmKk,phik := pSelmerGroup(k,Kp);

		Nbhds_oo cat:= [pAdicNbhd(X, OKpq!r[1], (OKpq!(a@@phik)) * piOKpq^v, k) : a in KmKk];
	end for;

	vprintf EtaleAlg: "computing nbhds\n";
	min_val_s := Min([Valuation(cs,p) : cs in Coefficients(ct - Evaluate(ct, 0)), ct in Coefficients(F)]);

	//if K = Q then separant computations will be performed over Q instead of
	//RationalsAsNumberField because it is significantly faster
	if Degree(K) eq 1 then
		KtoQ := Coercion(K, Q);
		SQ,StoSQ := ChangeRing(S, Q, KtoQ);
		RQ,RtoRQ := ChangeRing(R, SQ, StoSQ);
		Fcomp := RtoRQ(F);
		if BoundMethod eq "Default" then
			BoundMethod := "Separant";
		end if;
	else
		Fcomp := F;
		if BoundMethod eq "Default" then
			BoundMethod := "Difference";
		end if;
	end if;

	case BoundMethod:
		when "Separant":
			vprintf EtaleAlg: "computing general separant\n";
			gen_bound := SwitchVariables(SeparantUPol(Fcomp) div Parent(F).1^Degree(F));
		when "Derivative":
			vprintf EtaleAlg: "computing general derivative evaluated at roots\n";
			gen_bound := SwitchVariables(ValuationsInRootsOfUPol(Derivative(F), F));
		when "Difference":
			vprintf EtaleAlg: "computing general derivative evaluated at roots\n";
			gen_bound := SwitchVariables(ValuationsInRootsOfUPol(Derivative(F), F));
			vprintf EtaleAlg: "computing general difference of roots\n";
			Re<e> := PolynomialRing(S);
			Rx<x> := PolynomialRing(Re);
			_<y> := PolynomialRing(Rx);
			gen_diff := SwitchVariables(Resultant(Resultant(e - (x-y), Evaluate(F,y)), Evaluate(F,x)) div e^Degree(F));
		else:
			error "Option for BoundMethod not supported:", BoundMethod;
	end case;

	// Subdivide in smaller stable neighborhoods
	Nbhds := [<K!0,0>];
	Nbhds_end := []; // The neighborhoods that do not contain a root of the discriminant
	depth := 0;

	repeat
		Nbhds_new := [];
		depth +:= 1;
		vprintf EtaleAlg: "subdivision %o with %o neighbourhoods\n", depth, #Nbhds;
		for N in Nbhds do
			Np := phi(N[1]) + O(piKp^N[2]);
			error if N[2] ge Precision, "Precision too low:", Precision;

			if exists { Nd : Nd in Nbhds_disc | ContainedIn(Nd, Np) } then
				Nbhds_new cat:= Subdivide(N[1], N[2], N[2] + 1, p);
			elif exists { Nd : Nd in Nbhds_disc | ContainedIn(Np, Nd) } then
				//do nothing since Np is contained in one of the neighborhoods around a root of the discriminant
			else
				sN := Evaluate(gen_bound, N[1]);
				bN := Max([r[1] : r in ValuationsOfRoots(sN,Ideal(p))]);
				case BoundMethod:
					when "Separant":
						boundN := bN;
					when "Derivative":
						boundN := 2*bN;
					when "Difference":
						dN := Evaluate(gen_diff, N[1]);
						bdN := Max([r[1] : r in ValuationsOfRoots(dN,Ideal(p))]);
						boundN := bN + bdN;
				end case;

				if boundN - min_val_s lt N[2] then
					Append(~Nbhds_end, N);
				else
					Nbhds_new cat:= Subdivide(N[1], N[2], Floor(boundN - min_val_s + 1), p);
				end if;
			end if;
		end for;
		Nbhds := Nbhds_new;

		// Filter neighbourhoods
		Nbhds := [N : N in Nbhds | ContainsElementOfValuation(pAdicNbhd(X, OKpq!phi(N[1]), piOKpq^N[2], 1), CongrVal, MinVal)];
	until IsEmpty(Nbhds);

	// Add neighborhoods around the roots of the discriminant
	Nbhds := Nbhds_oo cat [pAdicNbhd(X, OKpq!phi(N[1]), piOKpq^N[2], 1) : N in Nbhds_end];

	// Filter neighborhoods
	Nbhds := [N : N in Nbhds | ContainsElementOfValuation(N, CongrVal, MinVal)];

	vprintf EtaleAlg: "computing isomorphism classes of %o etale algebras\n", #Nbhds;
	//use finite precision for last step
	KpP := ChangePrecision(Kp, Precision);
	psi := Coercion(Kp, KpP);
	SpP,StoSpP := ChangeRing(S, KpP, phi * psi);
	RpP,RtoRpP := ChangeRing(R, SpP, StoSpP);

	E := FindIsomorphismClasses([Evaluate(SwitchVariables(RtoRpP(F)),Representative(N)) : N in Nbhds] :
		Data := Nbhds, Hint := Hint);
	vprintf EtaleAlg: "%o isomorphism classes found among %o etale algebras\n", #E, #Nbhds;

	return E;
end intrinsic;

intrinsic Subdivide(x::FldNumElt, r::RngIntElt, n::RngIntElt, p::PlcNumElt) -> SeqEnum
{Subdivides a p-adic ball of the form x + O(p^r) into balls with radius p^n}
	if n le r then
		return [x];
	else
		K := Parent(x);
		OK := Integers(K);
		pi := UniformizingElement(p);

		Kp,KtoKp := Completion(K,p);
		OKp := Integers(Kp);
		pip := UniformizingElement(Kp);

		R := quo<OKp | pip^(n - r)>;
		phi := Coercion(OKp, R);
		S := quo<OK | pi^n>;

		//enumerating R can result in some duplicate elements,
		//so we will remove them first
		R_set := {y : y in R};

		return [ <K!(OK!S!x + pi^r * (y@@phi)@@KtoKp), n> : y in R_set ];
	end if;
end intrinsic;

intrinsic ContainedIn(x::FldPadElt, y::FldPadElt) -> BoolElt
{Returns whether x (as a p-adic ball) is contained in y}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;

intrinsic ContainedIn(x::RngPadElt, y::RngPadElt) -> BoolElt
{Returns whether x (as a p-adic ball) is contained in y}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;