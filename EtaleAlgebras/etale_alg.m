Z := Integers();
Q := Rationals();
EtRF := recformat< E : EtAlg, B0 : SeqEnum, Boo : SeqEnum >;

intrinsic Mu(f::RngUPolElt, g::RngUPolElt) -> .
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);

	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));

	vs := ValuationsOfRoots(res);
	//TODO: define Max([-Infinity()] cat ...) as Sup
	m, _ := Max([-Infinity()] cat [v[1] : v in vs]);
	return m;
end intrinsic;

intrinsic Mu(f::RngUPolElt, g::RngUPolElt, p::RngIntElt) -> RngIntElt
{}
	R := BaseRing(Parent(f));
	S<e> := PolynomialRing(R);
	T<t> := PolynomialRing(S);

	res := Resultant(e - Evaluate(f, t), Evaluate(g, t));

	vs := ValuationsOfRoots(res, p);
	//TODO: define Max([-Infinity()] cat ...) as Sup
	m, _ := Max([-Infinity()] cat [v[1] : v in vs]);
	return m;
end intrinsic;

intrinsic Bound1(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := 0;
	M := Max(M, k * Separant(f, g));
	M := Max(M, k * Separant(f));
	M := Max(M, k * Valuation(R!k) + k * Mu(Derivative(f), f) + (k-1) * Mu(g, f));

	S<s> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	F := Evaluate(f, t)^k - s * Evaluate(g, t);
	disc := LeadingCoefficient(F) * Discriminant(F);
	d := Degree(F) - Degree(f);
	c := Coefficient(disc, d);

	v := Valuation(Coefficient(disc, d));
	for i := d + 1 to Degree(disc) do
		M := Max(M, (Valuation(Coefficient(disc, i)) - v) / (d - i));
	end for;

	return M;
end intrinsic;

intrinsic Bound1(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, p::RngIntElt) -> RngElt
{}
	R := BaseRing(Parent(f));
	M := 0;
	M := Max(M, k * Separant(f, g, p));
	M := Max(M, k * Separant(f, p));
	M := Max(M, k * Valuation(R!k, p) + k * Mu(Derivative(f), f, p) + (k-1) * Mu(g, f, p));

	S<s> := PolynomialRing(R);
	T<t> := PolynomialRing(S);
	F := Evaluate(f, t)^k - s * Evaluate(g, t);
	disc := LeadingCoefficient(F) * Discriminant(F);
	d := Degree(F) - Degree(f);
	c := Coefficient(disc, d);

	v := Valuation(Coefficient(disc, d), p);
	for i := d + 1 to Degree(disc) do
		M := Max(M, (Valuation(Coefficient(disc, i), p) - v) / (d - i));
	end for;

	return M;
end intrinsic;

intrinsic EtaleAlgebraFamily(F::RngMPolElt, a::RngIntElt
	:D := LocalFieldDatabase()) -> .
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

	/*R := PolynomialRing(K, 4);
	RQ<e,sR,x,y> := PolynomialRing(Q, 4);
	dF := Derivative(F, t);
	printf "computing general separant\n";
	//time sep := Resultant(Resultant(e - (x - y) * Evaluate(dF, [sR, x]), Evaluate(F, [sR, x]), x), Evaluate(F, [sR, y]), y);
	sep := Resultant(Resultant(e - (x - y) * Evaluate(dF, [sR, x]), Evaluate(F, [sR, x]), x), Evaluate(F, [sR, y]), y);
	sep;
	coeffs := [PolynomialRing(K)![c2 + O(p)^1000 : c2 in Coefficients(UnivariatePolynomial(c))] : c in Coefficients(sep, 1) | c ne 0];
	coeffs;
	roots_Zp := IndexedSetToSequence({@ r[1] : r in Roots(c), c in coeffs | Valuation(r[1]) ge 0 @});
	//roots_Zp;
	GeneralizeBalls(roots_Zp);*/
	
	//TODO: change
	Precision := 500;
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
				Append(~C_end, X!c);
			elif n_roots_in_c eq 1 then
				Append(~C0, CreatePAdicNbhd(X, c, p^i, 1));
			else
				C_new cat:= [ c + (OKp!p)^i * OKp!x : x in ResidueSystem(K) ];
			end if;
		end for;
		C := C_new;
		i +:= 1;
	until IsEmpty(C);

	Ess := [];
	for c in C0 do
		c0 := Middle(c);
		pe := Radius(c);
		assert exists (r0) { r : r in [ro : ro in roots_Zp] | r in (K!c0 + O(K!pe)) };

		printf "computing around singular point: %o\n", r0;
		F0 := Evaluate(F, [r0 + pe * s, t]);
		//F0 := F0 / Coefficient(F0, t, Degree(F0, t)); //make monic in t
		f := UnivariatePolynomial(Evaluate(F, [r0, t]));

		//require Degree(F0, s) le 1: "Degree of g in s must be <= 1.";
		//TODO: prove I can remove the O(s^2) part
		g := -UnivariatePolynomial(Coefficient(F0, s, 1));
		Facf := Factorization(f);
		facs := [fac[1]^fac[2] : fac in Facf];
		_, cs := Xgcd([f div h : h in facs]);
		fcs := Zip(facs, cs);
		rs := [(fc[2] * g) mod fc[1] : fc in fcs];

		Es := [];
		for i := 1 to #Facf do
			fi := Facf[i][1];
			k := Facf[i][2];
			rsi := rs[i];
			B := [r0 + pe * X!b : b in EtaleAlgebraFamily0Nbhds(fi, rsi, k)];
			printf "computing étale algebras for %o polynomials\n", #B;
			E := EtaleAlgebraListIsomorphism2(F, B : D := D);
			for j := 1 to #E do
				E[j][2] := GeneralizeNbhds(E[j][2]);
			end for;
			Append(~Es, E);
		end for;

		Append(~Ess, Es);
	end for;

	return Ess;

end intrinsic;

intrinsic EtaleAlgebraFamily0Nbhds(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> SeqEnum[PadNbhdElt]
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

	vg := Valuation(Content(ChangeRing(g, Integers(K))));

	printf "computing separant\n";
	F1 := UnivariatePolynomial(Evaluate(F, s, p));
	sig1 := Separant(F1);
	prec := Max(0, Floor(sig1 - 1 - vg) + 1);

	printf "generating p-adic neighbourhoods\n";
	//TODO: prove that linearly extending the separant works
	B := [];
	for i := 1 to bound - 1 do
		B cat:= [X!(p^i * c + O(p^prec)) : c in quo<Integers(K) | p^prec> | Valuation(c) eq 0];
	end for;

	//TODO: change
	Precision := 500;
	OKp := quo<OK | p^Precision>;
	for i := 0 to k-1 do
		B cat:= [CreatePAdicNbhd(X, OKp!0, p^(bound+i) * K!c, k) : c in RepresentativesModuloPower(OK, k)];
	end for;

	return B;
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

intrinsic 'in'(x::FldPadElt, y::FldPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;

intrinsic 'in'(x::RngPadElt, y::RngPadElt) -> BoolElt
{Return whether x (as a p-adic ball) is contained in y.}
	return AbsolutePrecision(y) le AbsolutePrecision(x) and Precision(x - y) eq 0;
end intrinsic;
