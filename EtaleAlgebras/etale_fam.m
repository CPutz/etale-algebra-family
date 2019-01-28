//Constants
Z := Integers();
Q := Rationals();
Zx := PolynomialRing(Z);
Qx := PolynomialRing(Q);

/*intrinsic ValuationOfDerivative(P::RngUPolElt, Fs::FamNwtnPgonFace) -> SeqEnum[Tup]
{Returns the valuation of the derivative of P in the roots of the factor F of P}
	printf "Trying to determine |P'(t)| where P(t) = 0\n";
	printf "Trying around oo\n";
	IndentPush();
	try
		vs := ValuationOfPolynomial(Derivative(P), P, F);
		IndentPop();
		return vs;
	catch e
		printf "Error: %o\n", e`Object;
		IndentPop();
	end try;
	
	printf "Trying around 0\n";
	IndentPush();
	try
		t := Name(Parent(P),1);
		vs := ValuationOfPolynomial(t*Derivative(P) - Degree(P)*P, P, F);
		IndentPop();
		return vs;
	catch e
		printf "Error: %o\n", e`Object; IndentPop();
	end try;

	printf "Trying around 1\n";
	IndentPush();
	try
		t := Name(Parent(P),1);
		vs := ValuationOfPolynomial((t-1)*Derivative(P) - Degree(P)*P, P, F);
		IndentPop();
		return vs;
	catch e
		printf "Error: %o\n", e`Object;
		IndentPop();
	end try;

	return [];
end intrinsic;*/

intrinsic StructuralStability(P::RngUPolElt:
	Fs := Faces(FamilyOfNewtonPolygons(P))) -> SeqEnum[RngIntElt]
{Returns the constant mu (as a valuation) from the structural stability theorem}
	require ValuationE(LeadingCoefficient(P)) eq 0: "Argument 1 needs to be a monic polynomial:", P;

	vs := ValuationsOfPolynomial(Derivative(P), P);
	Mvs := {* v[1]^^v[2] : v in vs *};
	PMvs := Partitions(Mvs, [Length(F) : F in Fs]);

	for F in Fs do
		vsF := ValuationsOfPolynomial(Derivative(P), P, F);
		vsF;
	end for;

	if #PMvs eq 1 then
		mus := [];
		for Pvs in Rep(PMvs) do
			V := Parent(Rep(Pvs));
			v := V!(-Infinity());
			for v1 in MultisetToSet(Pvs) do
				v := Union(v, v1);
			end for;
			max := Max(v);
			if not IsConstant(max) then
				printf "mu depends on r\n";
			elif ISA(Type(max), Infty) then
				printf "mu is unbounded\n";
			end if;
			//mu := Q!max;
			mu := 2 * Q!Retrieve(Max(v));
			Append(~mus, Floor(mu + 1));
		end for;
		return mus;
	else
		Error("not implemented");
	end if;
end intrinsic;

intrinsic Inside(r1::RngPadElt, r2::RngPadElt) -> BoolElt
{}
	return IsZero(r1 - r2);
end intrinsic;

intrinsic Inside(r1::FldPadElt, r2::FldPadElt) -> BoolElt
{}
	return IsZero(r1 - r2);
end intrinsic;

intrinsic IsomorphismClassesFamEtaleUptoPrecision(P::RngUPolElt, prec::RngIntElt:
	r_min := PowerRange(BaseRing(Parent(P)))[1],
	r_max := PowerRange(BaseRing(Parent(P)))[2],
	D := LocalFieldDatabase()) -> SeqEnum[EtAlg]
{Computes the isomorphism classes of all fibres of P where we take all
parameters upto a certain p-adic precision}
	requirege prec, 0;
	printf "Compute isomorphism classes with p-adic precision %o\n", prec;
	R := Parent(P);
	Qp := BaseRing(BaseRing(R));
	p := Prime(Qp);
	PSet := ParameterSet(BaseRing(R));

    if prec eq 0 then
    	//B := [Zr!b + Qpr![O(Qp!p^1) : i in [1..rank]] : b in RSpace(Integers(p^1), rank)];
    	//B := [b : b in B | exists(t) {x : x in PSet | forall(i) {i : i in [1..rank] | Inside(x[i],b[i])}}];
		//b := B[1];
		//EvaluateParam(P, [p^r_min] cat Eltseq(b));
		//ForgetParam(EvaluateParam(P, [p^r_min] cat Eltseq(b)));
		//return [EtaleAlgebra(ForgetParam(EvaluateParam(P, [p^r_min] cat Eltseq(b))): W := <r_min, b>)];
		prec := 1;
	end if;
	vals := [Qx!ValuationE(LeadingCoefficient(a)) : a in Terms(P)];
	vals_a := [Qx!ValuationE(LeadingCoefficient(a)) : a in Terms(P) |
		&+ Prune(Reverse(Exponents(LeadingCoefficient(a)))) gt 0];
	//max valuation of r needed
	rs := [Roots(v - prec)[1][1] : v in vals | not IsConstant(v)];
	if not IsEmpty(rs) then
		Mr := Z!Ceiling(Max(rs));
	else
		Mr := 0;
	end if;
    min := Z!r_min;
    max := Max(min, Z!Min(r_max, Mr));
    Ps := [];
	Ws := [];

    printf "%o <= r <= %o for sufficient p-adic precision\n", min, max;
    for r := min to max do
    	//
    	prec_r := Max(1, Z!Ceiling(Max([prec - Evaluate(v,r) : v in vals_a])));
    	printf "r = %o and prec = %o\n", r, prec_r;
    	rank := Rank(BaseRing(R)) - 1;
	    Zr := RSpace(Z, rank);
	    Qpr := RSpace(Qp, rank);
		B := [Zr!b + Qpr![O(Qp!p^prec_r) : i in [1..rank]] : b in RSpace(Integers(p^prec_r), rank)];
	    B := [b : b in B | exists(t) {x : x in PSet | forall(i) {i : i in [1..rank] | Inside(x[i],b[i])}}];

    	//printf "case r = %o for sufficient p-adic precision\n", r;
		//Es cat:= [EtaleAlgebra(ForgetParam(EvaluateParam(P, [b, p^r])), <b,r>) : b in B];
		Ws cat:= [<r, b> : b in B];
		Ps cat:= [ForgetParam(EvaluateParam(P, [p^r] cat Eltseq(b))) : b in B];
    end for;
	printf "Computing isomorphism classes for %o polynomials\n", #Ps;
	return EtaleAlgebraListIsomorphism(Ps: D := D, W := Ws);
end intrinsic;


intrinsic IsomorphismClassesFamEtale(P::RngUPolElt:
	D := LocalFieldDatabase()) -> BoolElt, {}, {}
{Given a family of etale algebras P, returns a sequence of
isomorphism classes of all fibres}
	L := {};
	ER := ExtendedReals();
	read input, "Choose sample precision (default 3):";
	if input eq "" then
		prec := 3;
	else
		prec := StringToInteger(input);
	end if;
	samples := Set(IsomorphismClassesFamEtaleUptoPrecision(P, prec: D := D));
	printf "Found %o etale algebras.\n", #samples;

	printf "Trying around 0\n";
	b, L0 := IsomorphismClassesFamEtale(P, ER!0: D := D);
	if IsEmpty(L) then
		L join:= L0;
	elif b then
		L meet:= L0;
	end if;
	printf "\n";

	if L eq samples or forall(E) {E : E in L | assigned E`Witness} then
		if L eq samples then L := samples; end if; //witnesses
	printf "Conclusive about isomorphism classes. Found %o etale algebras\n", #L;
		return true, L, {};
	end if;

	printf "Trying around oo\n";
	b, Loo := IsomorphismClassesFamEtale(P, ER!Infinity(): D := D);
	if IsEmpty(L) then
		L join:= Loo;
	elif b then
		L meet:= Loo;
	end if;
	printf "\n";

	if L eq samples or forall(E) {E : E in L | assigned E`Witness} then
		if L eq samples then L := samples; end if; //witnesses
	printf "Conclusive about isomorphism classes. Found %o etale algebras\n", #L;
		return true, L, {};
	end if;
	
	printf "Trying around 1\n";
	b, L1 := IsomorphismClassesFamEtale(P, ER!1: D := D);
	if IsEmpty(L) then
		L join:= L1;
	elif b then
		L meet:= L1;
	end if;
	printf "\n";

	if L eq samples or forall(E) {E : E in L | assigned E`Witness} then
		if L eq samples then L := samples; end if; //witnesses
	printf "Conclusive about isomorphism classes. Found %o etale algebras\n", #L;
		return true, L, {};
	end if;

    Isw  := {E : E in L | assigned E`Witness} join samples;
    Isnw := {E : E in L | not assigned E`Witness};

    Isnw diff:= samples;

    if IsEmpty(Isnw) then
    	printf "Conclusive about isomorphism classes. Found %o etale algebras\n", #Isw;
    	return true, Isw, {};
    else
    	printf "Found %o etale algebras. Inconslusive about %o etale algebras\n", #Isw, #Isnw;
    	return false, Isw, Isnw;
    end if;
end intrinsic;


intrinsic IsomorphismClassesFamEtale(P::RngUPolElt, a::ExtReElt:
	D := LocalFieldDatabase()) -> BoolElt, {}
{Given a family of etale algebras P, returns a sequence of
isomorphism classes of all fibres}
	try
		if a eq Infinity() then
			P2 := MakeMonic(ReciprocalPolynomial(P));
		else
			t := Name(Parent(P), 1);
			q := Rationals()!a;
			x := Numerator(q);
			y := Denominator(q);
			P2 := MakeMonic(Evaluate(P, (t+x)/y));
		end if;
		L := IsomorphismClassesFamEtale2(P2, D);
		return true, L;
	catch e
		printf "Error: %o\n", e`Object;
		return false, {};
	end try;
end intrinsic;


intrinsic IsomorphismClassesFamEtale2(P::RngUPolElt, LFD::MyDB) -> {}
{Given a family of etale algebras P, returns a sequence of
isomorphism classes of all fibres}
	R := BaseRing(Parent(P));
	Qp := BaseRing(R);
	Zp := RingOfIntegers(Qp);
	p := Prime(Qp);
	ER := ExtendedReals();
	N := FamilyOfNewtonPolygons(P);

	range := PowerRange(R);
	if range[2] eq Infinity() then
		m := FamNewtonPolygonConverge(N);
		ranges := [<r, ER!r> : r in [range[1]..m-1]] cat [<m, ER!Infinity()>];
	else
		ranges := [<r, ER!r> : r in [range[1]..range[2]]];
	end if;

	Ls := [];

	//error if #Terms(LeadingCoefficient(P)) gt 1,
	//	"Cannot determine discrminant due to bug in Magma";
	//D := PolynomialRing(Z, 2) ! Discriminant(P);
	//Due to a bug in Magma we have to work over Z (or Q) here
	D := Discriminant(PolynomialRing(PolynomialRing(Z,2)) ! P);
	F, c := Factorization(D);
	disc_upto_squares := c * &* [f[1] : f in F | f[2] mod 2 eq 1];
	printf "Discriminant is %o upto squares\n", disc_upto_squares;
	FR := [<BaseRing(Parent(P))!r[1], r[2]> : r in F];
	valD := Valuation(Qp!c) + &+ [m[2] * ValuationE(m[1]) : m in FR];
	
	printf "Valuation of polynomial discriminant is %o\n", valD;

    for range in ranges do
    	Rr := PolynomialRing(ChangePowerRange(R, <range[1], range[1]>));
    	Pr := Rr!P;
    	if range[2] eq Infinity() then
    		printf "case r >= %o\n", range[1]; 
    	elif range[1] eq range[2] then
    		printf "case r = %o\n", range[1];
    		Pr := EvaluateParam(Pr, 1, p^(range[1]));
    	else
    		printf "case %o <= r <= %o\n", range[1], range[2];
    	end if;
    	IndentPush();

    	m := range[1];
    	Nr := FamilyOfNewtonPolygons(Pr);

    	Fs := FacesAt(Nr, m);
    	max_discs := [];
    	for factor in Fs do
    		n := Length(factor);
			s := Slope(factor);
			max_disc := valD + s*n*(n-1);
			Append(~max_discs, max_disc);
			printf "Valuation of discriminant is <= %o\n", max_disc;

    		/*printf "Factor %o\n", factor; IndentPush();
    		if n eq 1 then
    			printf "Factor is linear\n";
    			SetPrecision(factor, ER!0);
    			//SetEtalePossibilities(factor, [EtaleAlgebra(UnramifiedExtension(RingOfIntegers(Qp),1))]);
    		else
    			b, prec := StructuralStability(Pr, factor);
    			if b then
    				printf "Structural stability succeeded with precision = %o\n", prec;
    				//SetPrecision(factor, ER!prec);
    				//TODO: this is a hack
    				//if prec gt 3 then
    				//	SetPrecision(factor, ER!Infinity());
    				//	printf "p-adic precision too high for practical computations\n", prec;
    				//end if;
    				i := GetIndent();
    				read compute, "Do you want to compute upto this precision? (y/n)";
    				SetIndent(i);
    				//for j in [1..i] do
    				//	IndentPush();
    				//end for;
		    		if compute eq "n" then
		    			SetPrecision(factor, ER!Infinity());
		    		else
		    			SetPrecision(factor, ER!prec);
		    		end if;
    			else
    				printf "Structural stability failed\n";
    				SetPrecision(factor, ER!Infinity());
    			end if;
    		end if;
    		IndentPop(); printf "\n";*/
    	end for;


    	
    	prec_faces := [F : F in Fs | Precision(F) lt Infinity()];
    	if prec_faces eq Fs then
    		prec := Max([Precision(F) : F in prec_faces]);
    		if prec lt 0 then
    			prec := 0;
    		end if;
    		printf "Finite p-adic precision sufficient: %o\n", prec;
    		Ls cat:= IsomorphismClassesFamEtaleUptoPrecision(Pr, prec: r_min := range[1], r_max := range[2], D := LFD);
    	else
    		printf "Could not determine sufficient p-adic precision\n";

    		if not IsEmpty(prec_faces) then
    			prec := Max([Precision(F) : F in prec_faces]);
    			printf "Compute some factors with p-adic precision: %o\n", prec;
    			Es := IsomorphismClassesFamEtaleUptoPrecision(Pr, prec: r_min := range[1], r_max := range[2], D := LFD);
    			Cs := [Components(E) : E in Es];
    			pts := [Length(F) : F in prec_faces];
    			for C in Cs do
    				perms := Permutations([c[1] : i in [1..c[2]], c in C]);
    				perms := {@ p : p in perms @}; //remove duplicates
    				for p in perms do
    					Ess := [];
    					i := 1;
    					failed := false;
	    				for F in Fs do
	    					Es := [];
	    					d := Length(F);
	    					dsum := 0;
	    					repeat
	    						dsum +:= AbsoluteDegree(p[i]);
	    						Append(~Es, <p[i],1>);
	    						i +:= 1;
	    					until dsum ge d;
	    					if d eq dsum then
	    						Append(~Ess, Es);
	    					else
	    						failed := true;
	    						break;
	    					end if;
	    				end for;
	    				if not failed then
	    					for i := 1 to #Ess do
	    						Es := Ess[i];
	    						F := Fs[i];
		    					if Precision(F) lt Infinity() then
		    						AddEtalePossibilities(F, EtaleAlgebra(Es));
		    					end if;
	    					end for;
	    				end if;
    				end for;
    			end for;
    		end if;

	    	Ess := [];
	    	for F in Fs do
	    		if Precision(F) lt Infinity() then
	    			Append(~Ess, EtalePossibilities(F));
	    		else
	    			splittings := Splittings(F);

	    			splittings;

	    			Es := [Product(TupSeq(c)) : c in CartesianProduct([[EtaleAlgebra(K) : K in AllExtensions(LFD, Zp, d: Ediv := s[2])] : d in s[1]]), s in splittings];
	    			Append(~Ess, Es);
	    		end if;
	    	end for;

	    	candidates := [Product(TupSeq(c)) : c in CartesianProduct(Ess)];
	    	printf "Found %o etale algebras\n", #candidates;
	    	if IsConstant(disc_upto_squares) then
	    		bf := #candidates;
	    		candidates := [E : E in candidates | IsSquare(Z!disc_upto_squares * DiscriminantUptoSquares(E))];
	    		af := #candidates;
	    		printf "Eliminated %o etale algebras by comparing discriminants upto squares\n", bf - af;
	    	end if;

	    	max_discs_cons := [M : M in max_discs | IsConstant(M)];
	    	if not IsEmpty(max_discs_cons) then
	    		max := Z!Min(max_discs_cons);
	    		bf := #candidates;
	    		candidates := [E : E in candidates | Valuation(Discriminant(E)) le max];
	    		af := #candidates;
	    		printf "Eliminated %o etale algebras by max valuation discriminant\n", bf - af;
	    	end if;

	    	Ls cat:= candidates;
    	end if;
    	IndentPop(); printf "\n";
    end for;

    printf "Computing isomorphism classes\n";
    return Set(IsomorphismClassesEtale(Ls));
end intrinsic;