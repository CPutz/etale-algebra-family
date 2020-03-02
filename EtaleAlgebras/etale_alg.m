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

intrinsic EtaleAlgebraFamily(F::RngMPolElt, a::RngIntElt) -> .
{}
	P := Parent(F);
	K := BaseRing(P);
	require ISA(Type(K), FldPad): "Argument 1 must be a polynomial over a p-adic field";
	require Rank(P) eq 2: "Argument 1 must be a polynomial in 2 variables";

	disc := UnivariatePolynomial(Discriminant(F, 2));
	roots_Zp := [r : r in Roots(disc) | Valuation(r[1]) ge 0];
	p := UniformizingElement(K);

	C := [O(K!1)];
	C_end := [];
	C0 := [];
	i := 0;
	repeat
		C_new := [];
		for c in C do
			cp := ChangePrecision(c, i+1);
			//TODO: maybe relax the condition to Zp?
			if not HasRoot(Evaluate(disc, cp + p^i * Parent(disc).1))then
			//if forall { r : r in roots_Z | not (Qp!r in c) } then
				Append(~C_end, c);
			elif #{ r : r in roots_Zp | r[1] in c } eq 1 then
				Append(~C0, <c, i>);
			else
				C_new cat:= [ cp + p^i * x + O(p)^(i+1) : x in ResidueSystem(K) ];
			end if;
		end for;
		C := C_new;
		i +:= 1;
	until IsEmpty(C);

	C_end;
	C0;
	
	Ess := [];

	for ci in C0 do
		c0 := ci[1];
		i := ci[2];
		error if not exists (r0) { r : r in [ro[1] : ro in roots_Zp] | r in c0 },
			"This should not happen: c0 should contain a unique zero of the discriminant.";

		printf "computing around root: %o\n", r0;
		s := P.1;
		t := P.2;
		F0 := Evaluate(F, [p^i * s + r0, t]);
		f := UnivariatePolynomial(Evaluate(F0, [0, t]));

		//require Degree(F0, s) le 1: "Degree of g in s must be <= 1.";
		//TODO: prove I can remove the O(s^2) part
		g := UnivariatePolynomial(Coefficient(F0, s, 1));
		Facf := Factorization(f);
		facs := [fac[1]^fac[2] : fac in Facf];
		_, cs := Xgcd([f div h : h in facs]);
		fcs := Zip(facs, cs);
		rs := [fc[2] * g mod fc[1] : fc in fcs];

		Es := [ EtaleAlgebraFamily0(Facf[i][1], rs[i], Facf[i][2], a) : i in [1..#facs] ];
		for i := 1 to #Es do
			for j := 1 to #Es[i] do
				Es[i,j]`B0 := [ (c - r0) / p^i : c in Es[i,j]`B0 ];
			end for;
		end for;

		/*Ess_new := [];
		for Es1 in Es do
			Es_new := [];
			for E in Es1 do
				W_new := [<p^i * c[1] + r0, c[2] - i> : c in Witness(E)];
				E_new := E;
				ChangeWitness(~E_new, W_new);
				Append(~Es_new, E_new);
			end for;
			Append(~Ess_new, Es_new);
		end for;

		Append(~Ess, Ess_new);*/
		Append(~Ess, Es);
	end for;

	return Ess;

end intrinsic;

intrinsic EtaleAlgebraFamily0(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, a::RngIntElt) -> .
{}
	B0, Boo := EtaleAlgebraFamily0Nbhds(f, g, k);

	printf "computing étale algebras for %o polynomials\n", #B0 + #Boo;

	D := LocalFieldDatabaseOctic2Adics();
	return EtaleAlgebraListIsomorphism2([f^k - c*g : c in B0], B0, [f^k - c[1]*g : c in Boo], Boo: D := D);
end intrinsic

intrinsic EtaleAlgebraFamily0Nbhds(f::RngUPolElt, g::RngUPolElt, k::RngIntElt) -> SeqEnum, SeqEnum
{}
	require Degree(g) le k * Degree(f): "Degree of f^k must be at least the degree of g";
	K := CoefficientRing(f);
	require Parent(f) eq Parent(g): "Argument 1 and 2 must be defined over the same field";
	require ISA(Type(K), FldPad): "Argument 1 and 2 must be defined over a p-adic field";
	require Valuation(LeadingCoefficient(f)) eq 0: "Argument 1 must be monic (the leading coefficient must be a unit)";

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

	B := Z!Bound1(f, g, k);
	printf "bound: %o\n", B;

	vg := Valuation(Content(ChangeRing(g, Integers(K))));

	printf "computing separant\n";
	F1 := UnivariatePolynomial(Evaluate(F, s, p));
	sig1 := Separant(F1);
	prec := Floor(sig1 - 1 - vg) + 1;

	printf "generating p-adic neighbourhoods\n";
	//TODO: prove that linearly extending the separant works
	B0 := [];
	for i := 1 to B - 1 do
		B0 cat:= [p^i * c : c in quo<Integers(K) | p^prec> | Valuation(c) eq 0];
	end for;

	Boo := [];
	for i := 0 to k-1 do
		Boo cat:= [<p^(B+i) * c, k> : c in quo<Integers(K) | p^prec> | Valuation(c) eq 0];
	end for;

	return B0, Boo;
end intrinsic;

FactorizationStructureList := function(L)
    return Sort([<Degree(Ki[1]), Ki[2]> : Ki in L]);
end function;

intrinsic EtaleAlgebraListIsomorphism2(L0::SeqEnum[RngUPolElt], B0::SeqEnum[FldPadElt],
	Loo::SeqEnum[RngUPolElt], Boo::SeqEnum[Tup] :
	D := LocalFieldDatabase()) -> SeqEnum[EtAlg]
{Creates a list of etale algebra given a sequence of polynomials over a local field}
    require #L0 eq #B0: "L0 and W0 must have the same length";
    require #Loo eq #Boo: "Loo and Woo must have the same length";
    if IsEmpty(L0) and IsEmpty(Loo) then
        return [];
    end if;

    Res := [];
    if not IsEmpty(L0) then
    	K := BaseRing(L0[1]);
    else
    	K := BaseRing(Loo[1]);
    end if;
    OK := RingOfIntegers(K);
    R := PolynomialRing(OK);

    Fs0 := [<Factorization(R ! MakeMonicIntegral(L0[i])), L0[i], B0[i]> : i in [1..#L0]];
    Fsoo := [<Factorization(R ! MakeMonicIntegral(Loo[i])), Loo[i], Boo[i]> : i in [1..#Loo]];
    Fstructures := {@ FactorizationStructureList(F) : F in [f[1] : f in Fs0] cat [f[1] : f in Fsoo] @};
    
    Fss0 := [[F : F in Fs0 | FactorizationStructureList(F[1]) eq Fstruct] : Fstruct in Fstructures];
    Fssoo := [[F : F in Fsoo | FactorizationStructureList(F[1]) eq Fstruct] : Fstruct in Fstructures];

    for Fstruct in Fstructures do
    	res := [];

    	Fss0 := [F : F in Fs0 | FactorizationStructureList(F[1]) eq Fstruct];
    	for FP in Fss0 do
            found := false;
            //for E in res do
            for i := 1 to #res do
            	E := res[i];
                if IsDefiningPolynomialEtale(E`E, FP[1]) then
                    found := true;
                	found_i := i;
                    break;
                end if;
            end for;
            if found then //add witness
            	res[found_i]`B0 := Append(res[found_i]`B0, FP[3]);
            else
                Append(~res, rec< EtRF | E := EtaleAlgebra(FP[2]: D := D), B0 := [FP[3]], Boo := [] >);
            end if;
        end for;

        Fssoo := [F : F in Fsoo | FactorizationStructureList(F[1]) eq Fstruct];
    	for FP in Fssoo do
            found := false;
            //for E in res do
            for i := 1 to #res do
            	E := res[i];
                if IsDefiningPolynomialEtale(E`E, FP[1]) then
                    found := true;
                	found_i := i;
                    break;
                end if;
            end for;
            if found then //add witness
            	res[found_i]`Boo := Append(res[found_i]`Boo, FP[3]);
            else
                Append(~res, rec< EtRF | E := EtaleAlgebra(FP[2]: D := D), B0 := [], Boo := [FP[3]] >);
            end if;
        end for;

    	Res cat:= res;
    end for;

    /*for C in Fss0 do
        res := [];
        for FP in C do
            found := false;
            Ec := 0;
            //for E in res do
            for i := 1 to #res do
            	E := res[i];
                if IsDefiningPolynomialEtale(E`E, FP[1]) then
                    found := true;
                	found_i := i;
                    break;
                end if;
            end for;
            if found then //add witness
            	res[found_i]`B0 := Append(res[found_i]`B0, FP[3]);
            else
                Append(~res, rec< EtRF | E := EtaleAlgebra(FP[2]: D := D), B0 := [FP[3]], Boo := [] >);
            end if;
        end for;
        Res cat:= res;
    end for;*/

    return Res;
end intrinsic;








intrinsic EtaleAlgebraFamily(F::RngMPolElt, p::RngIntElt, a::RngIntElt) -> .
{}
	P := Parent(F);
	R := BaseRing(P);
	require ISA(Type(R), RngInt): "Argument 1 must be a polynomial over Z";
	require Rank(P) eq 2: "Argument 1 must be a polynomial in 2 variables";
	require IsPrime(p): "Argument 2 must be prime";

	K := FieldOfFractions(R);

	//Pe<e> := PolynomialRing(R);
	//Ps<s> := PolynomialRing(Pe);
	//Pxy<x, y> := PolynomialRing(Ps, 2);
	//dF := Derivative(F, 2);
	//seps := Ps!(Resultant(Resultant(e - Evaluate(dF, [s, x]) * (x - y), Evaluate(F, [s, x]), 1), Evaluate(F, [s, y]), 2) div e^Degree(F));

	g := F - Evaluate(F, [0, P.2]);
	vg := Valuation(Content(g), p);

	disc := UnivariatePolynomial(Discriminant(F, 2));
	/*rZ := Roots(disc, Z);
	roots_Z := [r[1] : r in rZ];
	Factorization(disc);
	ValuationsOfRoots(disc, p);
	num_roots_Z := &+([0] cat [v[2] : v in rZ]);
	num_roots_Zp := &+([0] cat [v[2] : v in ValuationsOfRoots(disc, p) | v[1] ge 0]);
	require num_roots_Z eq num_roots_Zp: "The roots of the discriminant of F over Zp-bar must be a root over Z";*/

	Qp := pAdicField(p, 500);
	roots_Zp := [r : r in Roots(disc, Qp) | Valuation(r[1]) ge 0];

	C := [O(Qp!1)];
	C_end := [];
	C0 := [];
	i := 0;
	repeat
		C_new := [];
		for c in C do
			//TODO: maybe relax the condition to Zp?
			if not HasRoot(Evaluate(disc, Z!c + p^i * Parent(disc).1), Qp)then
			//if forall { r : r in roots_Z | not (Qp!r in c) } then
				Append(~C_end, c);
			elif #{ r : r in roots_Zp | r[1] in c } eq 1 then
				Append(~C0, <c, i>);
			else
				C_new cat:= [ Z!c + p^i * Z!x + O(Qp!p)^(i+1) : x in Integers(p) ];
			end if;
		end for;
		C := C_new;
		i +:= 1;
	until IsEmpty(C);

	C_end;
	C0;
	
	Ess := [];

	for ci in C0 do
		c0 := ci[1];
		i := ci[2];
		error if not exists (r0) { r : r in [ro[1] : ro in roots_Zp] | r in c0 },
			"This should not happen: c0 should contain a unique zero of the discriminant.";

		printf "computing around root: %o\n", r0;

		Pp<s, t> := PolynomialRing(Qp, 2);
		F0 := Evaluate(F, [p^i * s + r0, t]);
		f := UnivariatePolynomial(Evaluate(F0, [0, t]));

		//require Degree(F0, s) le 1: "Degree of g in s must be <= 1.";
		//TODO: prove I can remove the O(s^2) part
		g := UnivariatePolynomial(Coefficient(F0, s, 1));
		Facf := Factorization(f);
		facs := [fac[1]^fac[2] : fac in Facf];
		_, cs := Xgcd([f div h : h in facs]);
		fcs := Zip(facs, cs);
		rs := [fc[2] * g mod fc[1] : fc in fcs];

		"roots";
		//F1 := Evaluate(Facf[1][1], t)^Facf[1][2] - s * Evaluate(rs[1], t);
		//disc1 := UnivariatePolynomial(Discriminant(F1, 2));

		//Factorization(disc1);
		//F1;

		Es := [ EtaleAlgebraFamily0(Facf[i][1], rs[i], Facf[i][2], a) : i in [1..#facs] ];
		
		Ess_new := [];
		for Es1 in Es do
			Es_new := [];
			for E in Es1 do
				W_new := [<p^i * c[1] + r0, c[2] - i> : c in Witness(E)];
				E_new := E;
				ChangeWitness(~E_new, W_new);
				Append(~Es_new, E_new);
			end for;
			Append(~Ess_new, Es_new);
		end for;

		Append(~Ess, Ess_new);
	end for;

	return Ess;

end intrinsic;

/*intrinsic EtaleAlgebraFamily0(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, a::RngIntElt) -> .
{Computes the isomorphism classes of f^k - s*g where s varies over p^(ar) * Zp^* with r >= 1}
	require Degree(g) le k * Degree(f): "Degree of f^k must be at least the degree of g";
	K := CoefficientRing(f);
	require Parent(f) eq Parent(g): "Argument 1 and 2 must be defined over the same field";
	require ISA(Type(K), FldPad): "Argument 1 and 2 must be defined over a p-adic field";
	require Valuation(LeadingCoefficient(f)) eq 0: "Argument 1 must be monic (the leading coefficient must be a unit)";

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
	F;
	disc := UnivariatePolynomial(Discriminant(F, t));
	"disc";
	disc;
	g;
	Factorization(disc);
	Roots(Factorization(disc)[2][1], K);
	Roots(disc);
	ValuationsOfRoots(disc);
	v0 := &+([0] cat [r[2] : r in Roots(disc) | Valuation(r[1]) ge 0]);
	v0;
	require v0 eq Degree(f) * (k - 1): "F(s,t) may only have s = 0 as a singular point in Zp";

	B := Bound1(f, g, k);
	B;

	Cs := [];
	Cs2 := [];
	vg := Valuation(Content(ChangeRing(g, Integers(K)))); vg;

	F1 := UnivariatePolynomial(Evaluate(F, s, p^a));
	sig1 := Separant(F1);
	prec := Floor(sig1 - a - vg) + 1;

	//TODO: prove that linearly extending the separant works
	for i := 1 to Floor(B / a) do
		Cs cat:= [p^(a*i) * c : c in quo<K | p^prec> | Valuation(c) eq 0];
		Cs2 cat:= [<K!c, a*i> : c in quo<K | p^prec> | Valuation(c) eq 0];
	end for;

	Cs;

	if IsEmpty(Cs) then
		Cs := [p^a];
	end if;

	D := LocalFieldDatabaseOctic2Adics();
	return EtaleAlgebraListIsomorphism([f^k - c*g : c in Cs] : D := D, W := Cs2);
end intrinsic;*/

/*intrinsic EtaleAlgebraFamily0(F::RngMPolElt) -> .
{}
	R := Parent(F);
	s := R.1;
	t := R.2;
	K := BaseRing(R);
	require ISA(Type(K), FldPad): "Argument 1 must be a polynomial over a p-adic field";
	require Rank(R) eq 2: "Argument 1 must be a polynomial in 2 variables";

	//TODO: reduction to f - s*g
	f := UnivariatePolynomial(Evaluate(F, s, 0));
	g := UnivariatePolynomial(-Coefficient(F - Evaluate(F, s, 0), s, 1));

	//TODO: resolve this case
	require Gcd(f, g) eq 1: "f and g must be coprime.";

	L := [];
	f2 := f;
	Fac := Factorization(f2);
	while not IsEmpty(Fac) do
		Fac;
		f1 := Fac[1,1] ^ Fac[1,2];
		f2 := f2 div f1;

		_, c2, c1 := Xgcd(f1, f2);
		c2 * f1 + c1 * f2;

		r1 := c1 * g mod f1;
		r2 := c1 * g mod f2;
		r1; r2;

		Fac1 := Factorization(f1);
		Append(~L, <Fac1[1,1], Fac[1,2], r1>);

		Fac := Factorization(f2);
	end while;

	return L;
end intrinsic;*/

/*intrinsic EtaleAlgebraFamily(f::RngUPolElt, g::RngUPolElt, k::RngIntElt, a::RngIntElt, p::RngIntElt) -> .
{Computes the isomorphism classes of f^k - s*g where s varies over p^(ar) * Zp^* with r >= 1}
	require Degree(g) le k * Degree(f): "Degree of f^k must be at least the degree of g";
	K := CoefficientRing(f);
	require CoefficientRing(g) eq K: "Argument 1 and 2 must have the same coefficient ring";
	require ISA(Type(K), RngInt): "Argument 1 and 2 must be defined over Z";
	
	R<s0,t0> := PolynomialRing(K, 2);
	phi := hom<Parent(f) -> R | Parent(f).1 -> t0>;
	F := phi(f)^k - s0 * phi(g);
	disc := UnivariatePolynomial(Discriminant(F, t0));
	Factorization(disc);
	ValuationsOfRoots(disc, p);
	v0 := &+([0] cat [v[2] : v in ValuationsOfRoots(disc, p) | v[1] gt 0]);
	require v0 eq Degree(f) * (k - 1): "F(s,t) may only have s = 0 as a singular point in p*Zp";

	B := Bound1(f, g, k, p);
	B;

	Cs := [];
	Cs2 := [];
	vg := Valuation(Content(g), p);
	for i := 1 to Floor(B / a) do
		F0 := UnivariatePolynomial(Evaluate(F, s0, p^(a*i)));

		sig := Separant(F0, p);
		prec := Floor(sig - a * i - vg) + 1;

		Cs cat:= [p^(a*i) * Z!c : c in Integers(p^prec) | Z!c mod p ne 0];
		Cs2 cat:= [<Z!c, a*i> : c in Integers(p^prec) | Z!c mod p ne 0];
	end for;

	Cs;

	if IsEmpty(Cs) then
		Cs := [p^a];
	end if;

	Qp := pAdicField(p, 500);
	Rp<sp, tp> := PolynomialRing(Qp, 2);
	phi2 := hom<R -> Rp | sp, tp>;
	Fp := phi2(F);

	D := LocalFieldDatabaseOctic2Adics();
	return EtaleAlgebraListIsomorphism([UnivariatePolynomial(Evaluate(Fp, sp, c)) : c in Cs] : D := D, W := Cs2);
end intrinsic;*/

/*intrinsic EtaleAlgebraIsomorphismClasses(F::RngMPolElt, p::RngIntElt) -> .
{}
	R := Parent(F);
	s := R.1;
	t := R.2;
	K := BaseRing(R);
	require ISA(Type(K), FldRat): "Argument 1 must be a polynomial over the rationals";
	require Rank(R) eq 2: "Argument 1 must be a polynomial in 2 variables";

	disc := UnivariatePolynomial(Discriminant(F, t));
	Factorization(disc);

	//error if not Splits(disc, Q), "Singular points of f (with respect to the family paramater) must be rational.";

	roots := [r[1] : r in Roots(disc, Q)];
	roots;

	f := UnivariatePolynomial(Evaluate(F, s, 0));
	//TODO: This should be factorization over Qp
	Fac := Factorization(f);
	//TODO: Handle general case
	error if #Fac gt 1, "F(0, t) must be a perfect power of an irreducible polynomial over Q";

	h := Fac[1,1];
	k := Fac[1,2];
	g := UnivariatePolynomial(-(F - Evaluate(F, s, 0)) div s);

	sh := Separant(h, p);
	shg := Separant(h, g, p);

	B := Floor(Max([0, k * sh, k * shg, k * Valuation(k, p) + k * Mu(Derivative(h), h, p) + (k-1) * Mu(g, h, p)]));

	Qp := pAdicField(p);
	C := [p * e : e in Subdivide(Qp, B + 1)];

	Qpst := ChangeRing(R, Qp);
	sp := Qpst.1;
	tp := Qpst.2;
	Fp := Qpst!F;

	Es := [EtaleAlgebra(UnivariatePolynomial(Evaluate(Fp, sp, x))) : x in C];

	return Es;
end intrinsic;*/

intrinsic Splits(f::RngUPolElt, R::Rng) -> BoolElt
{Returns whether f splits over the ring R.}
	return &+([0] cat [r[2] : r in Roots(f, R)]) eq Degree(f);
end intrinsic;

intrinsic GeneralizeBalls(S::SeqEnum[FldPadElt]) -> SeqEnum[FldPadElt]
{}
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
