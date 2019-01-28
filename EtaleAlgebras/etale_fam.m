//Constants
Z := Integers();
Q := Rationals();
Zx := PolynomialRing(Z);
Qx := PolynomialRing(Q);

//Add attributes to multivariate polynomial rings which
//we use to represent our families of etale algebras
declare attributes RngMPol: PowerRange, ParameterSet;
declare attributes RngUPol: PowerRange;

intrinsic CreateParameterSpace(R::RngUPol, r::<>) -> RngUPol
{Assigns a range for the parameter of R}
	require r[1] ge 0:
		"First entry of Argument 2 must be >= 0";
	R`PowerRange := r;
	return R;
end intrinsic;

intrinsic CreateParameterSpace(R::RngMPol, r::<>, S::SetCart) -> RngMPol
{Assigns a range for the power parameter and parameter set S to R}
	require NumberOfComponents(S) eq Rank(R) - 1:
		"Rank of Argument 1 must be one less than the number of components of Argument 3";
	require r[1] ge 0:
		"First entry of Argument 2 must be >= 0";
	R`PowerRange := r;
	R`ParameterSet := S;
	return R;
end intrinsic;

intrinsic PowerRange(R::RngUPol) -> <>
{The Range of the variable of R}
	return R`PowerRange;
end intrinsic;

intrinsic PowerRange(R::RngMPol) -> <>
{The Range of the power variable of R}
	return R`PowerRange;
end intrinsic;

intrinsic ParameterSet(R::RngMPol) -> SetCart
{The parameter set of R}
	return R`ParameterSet;
end intrinsic;

intrinsic DropParameterSet(R::RngMPol) -> RngUPol
{Forgets all parameters of R except for the first}
	rs := PowerRange(R);
	S := PolynomialRing(BaseRing(R));
	return CreateParameterSpace(S, rs);
end intrinsic;

intrinsic ChangePowerRange(R::RngMPol, r::<>) -> RngMPol
{Forgets all parameters of R except for the first}
	ps := ParameterSet(R);
	S := PolynomialRing(BaseRing(R), Rank(R));
	return CreateParameterSpace(S, r, ps);
end intrinsic;

intrinsic IsConstant(P::RngUPolElt) -> BoolElt
{Determines whether a univariate polynomial is constant}
	return ConstantCoefficient(P) eq P;
end intrinsic;

intrinsic IsConstant(P::RngMPolElt) -> BoolElt
{Determines whether a multivariate polynomial is constant}
	return ConstantCoefficient(P) eq P;
end intrinsic;

intrinsic IsConstant(P::Infty) -> BoolElt
{}
	return true;
end intrinsic;

intrinsic ConstantCoefficient(P::RngMPolElt) -> RngElt
{Returns the constant coefficient of a multivariate polynomial}
	return Evaluate(P, [0 : i in [1..Rank(Parent(P))]]);
end intrinsic;

intrinsic Evaluate(P::RngUPolElt, m::Infty) -> Infty
{Evaluate a polynomial P at +-Infinity}
	if IsConstant(P) then
		return ConstantCoefficient(P);
	else
		return Sign(P) * Sign(m)^Degree(P) * Infinity();
	end if;
end intrinsic;

intrinsic Max(m1::RngUPolElt, m2::Infty) -> .
{Maximum of a linear polynomial and +-Infinity}
	if Sign(m2) gt 0 then
		return m2;
	else
		return m1;
	end if;
end intrinsic;
intrinsic Max(m1::Infty, m2::RngUPolElt) -> .
{Maximum of a linear polynomial and +-Infinity}
	return Max(m2, m1);
end intrinsic;

intrinsic Min(m1::RngUPolElt, m2::Infty) -> .
{Minimum of a linear polynomial and +-Infinity}
	if Sign(m2) lt 0 then
		return m2;
	else
		return m1;
	end if;
end intrinsic;
intrinsic Min(m1::Infty, m2::RngUPolElt) -> .
{Minimum of a linear polynomial and +-Infinity}
	return Min(m2, m1);
end intrinsic;

intrinsic Max(m1::RngUPolElt, m2::RngUPolElt) -> RngUPolElt
{Minimum of a two linear polynomials}
	require Degree(m1) le 1: "Argument 1 must have degree <= 1";
	require Degree(m2) le 1: "Argument 2 must have degree <= 1";
	require Sign(m1) ge 0: "Argument 1 must have non-negative leading coeffient";
	require Sign(m2) ge 0: "Argument 2 must have non-negative leading coeffient";
	require Degree(m2) le 1: "Argument 2 must have degree <= 1";
	require Parent(m1) eq Parent(m2): "Polynomials must have the same parent";
	R := Parent(m1);
	range := PowerRange(R);
	if Coefficient(m1, 1) lt Coefficient(m2, 1) then
		Swap(~m1, ~m2);
	end if;

	f := m1 - m2;
	v := Evaluate(f, range[1]);
	if v lt 0 then
		return m1 - v;
	else
		return m1;
	end if;
end intrinsic;

intrinsic Min(m1::RngUPolElt, m2::RngUPolElt) -> RngUPolElt
{Minimum of a two linear polynomials}
	require Degree(m1) le 1: "Argument 1 must have degree <= 1";
	require Degree(m2) le 1: "Argument 2 must have degree <= 1";
	require Sign(m1) ge 0: "Argument 1 must have non-negative leading coeffient";
	require Sign(m2) ge 0: "Argument 2 must have non-negative leading coeffient";
	require Degree(m2) le 1: "Argument 2 must have degree <= 1";
	require Parent(m1) eq Parent(m2): "Polynomials must have the same parent";
	R := Parent(m1);
	range := PowerRange(R);
	if Coefficient(m1, 1) lt Coefficient(m2, 1) then
		Swap(~m1, ~m2);
	end if;

	f := m1 - m2;
	v := Evaluate(f, range[1]);
	if v lt 0 then
		return m2 + v;
	else
		return m2;
	end if;
end intrinsic;

intrinsic Sign(f::RngUPolElt[FldRat]) -> RngIntElt
{Sign of the leading coefficient of the univariate integer polynomial f}
	if f eq 0 then
		return 0;
	else
		return Sign(LeadingCoefficient(f));
	end if;
end intrinsic;

intrinsic Valuation2(P::RngUPolElt) -> <>
{The minimal and maximal valuation of P}
	if P eq 0 then
		return <Infinity(), Infinity()>;
	elif assigned Parent(P)`PowerRange then
		S := Parent(P);
		range := PowerRange(S);
		d := Valuation(P); //largest d such that &^d | P
		cd := Coefficient(P, d);
		vd := Valuation(cd);

		min_r := range[1];
		for s in Support(P) do
			if s gt d then
				v := Valuation(Coefficient(P, s));
				r := Ceiling(Q!(vd - v) / (s - d));
				min_r := Max(min_r, r);
			end if;
		end for;

		R := CreateParameterSpace(PolynomialRing(Z),range);
		min := R.1 * d + vd;
		if RelativePrecision(cd) gt 0 then
			max := min;
		else
			max := Infinity();
		end if;

		u := UniformizingElement(BaseRing(S));
		for r := range[1] to min_r-1 do
			v := R!Valuation(Evaluate(P,u^r));
			min := Min(min, v);
		end for;

		return <min, max>;
	else
		Error("Variable of Argument 1 must have a range");
	end if;
end intrinsic;

intrinsic Valuation2E(P::RngUPolElt) -> RngUPolElt
{Finds the valuation of P, and gives an error if it cannot determine it}
	v := Valuation(P);
	error if v[1] ne v[2], "Could not determine valuation of", P;
	return v[1];
end intrinsic;

intrinsic Valuation(m::RngMPolElt) -> <>
{The minimal and maximal valuation of m}
	R := Parent(m);
	require ISA(Type(BaseRing(R)), FldPad) or
			ISA(Type(BaseRing(R)), RngPad):
		"Parent of Argument 1 must be defined over a p-adic field of ring";
	require assigned Parent(m)`ParameterSet:
		"Parent of Argument 1 must be a parameter space";

	min :=  Infinity();
	max := -Infinity();
	for s in ParameterSet(R) do
		r := Name(R, 1);
		e := UnivariatePolynomial(Evaluate(m, [r] cat TupSeq(s)));
		e := DropParameterSet(R) ! e;
		v := Valuation2(e);
		min := Min(min, v[1]);
		max := Max(max, v[2]);
	end for;
	return <min, max>;
end intrinsic;

intrinsic ValuationE(m::RngMPolElt) -> RngUPolElt
{Finds the valuation of m, and gives an error if it cannot determine it}
	v := Valuation(m);
	error if v[1] ne v[2], "Could not determine valuation of", m;
	return v[1];
end intrinsic;

intrinsic ValuationsOfRoots2(P::RngUPolElt) -> SeqEnum[Tup]
{Gives the valuations of the roots of P}
	N := FamilyOfNewtonPolygons(P);
	range := PowerRange(BaseRing(Parent(P)));
	r := range[1];
	require FamNewtonPolygonConverged(N, r):
		"Newton polygon of Argument 1 is not converged over:", range;
	return [<-Slope(F), Length(F)> : F in FacesAt(N, r)];
end intrinsic;

intrinsic EvaluateParam(P::RngUPolElt, x::.) -> RngUPolElt
{Evaluates the parameters of P at x}
	return Parent(P) ! [Evaluate(c, x) : c in Coefficients(P)];
end intrinsic;

intrinsic EvaluateParam(P::RngUPolElt, i::RngIntElt, x::.) -> RngUPolElt
{Evaluates the i-th parameter of P at x}
	return Parent(P) ! [Evaluate(c, i, x) : c in Coefficients(P)];
end intrinsic;

intrinsic ForgetParam(P::RngUPolElt) -> RngUPolElt
{Defines P as a polynomial over the p-adic base field if P does not depend
on a and r}
	R := BaseRing(BaseRing(Parent(P)));
	S := PolynomialRing(R);
	error if exists(t) {c : c in Coefficients(P) | not IsConstant(c)},
		"Polynomial depends on a or r";
	return S ! [ConstantCoefficient(c) : c in Coefficients(P)];
end intrinsic;

intrinsic Translate(P::RngUPolElt, r::RngElt) -> RngUPolElt
{Translates P by r}
	t := Name(Parent(P), 1);
	return Evaluate(P, t - r);
end intrinsic;

intrinsic ReciprocalScale(P::RngUPolElt, r::RngElt) -> RngUPolElt
{Scales the coefficients of P by r with reverse weights}
	d := Degree(P);
	return Parent(P) ! [r^(d-c) * Coefficient(P, c) : c in [0..d]]; 
end intrinsic;

intrinsic ValuationOfPolynomial(P::RngUPolElt, D::RngUPolElt, F::FamNwtnPgonFace) -> SeqEnum[Tup]
{Returns the valuations of P in the roots of a factor F of D}
	vmin := Infinity();
	vmax := -Infinity();
	range := PowerRange(BaseRing(Parent(D)));
	r := range[1];
	vF := -Slope(F);
	
	for m in Support(P) do
		vm := Valuation(Coefficient(P, m));
		vmin := Min(vmin, vm[1] + m*vF);
		vmax := Max(vmax, vm[2] + m*vF);
	end for;

	if vmin eq vmax then
		return [<vmin, Length(F)>];
	end if;

	try 
		R := BaseRing(Parent(P));
		S<c> := PolynomialRing(R);
		Rc := PolynomialRing(S);
		Pc := Rc ! Coefficients(P);
		Dc := Rc ! Coefficients(D);

		T := PolynomialRing(PolynomialRing(PolynomialRing(Z,Rank(R))));
		res := S!Resultant(T!(c - Pc), T!Dc);

		vals := ValuationsOfRoots2(res);
		vs := [v : v in vals | vmin le v[1] and v[1] le vmax];
		vs;
		if &+ [v[2] : v in vs] eq Length(F) then
			return vs;
		end if;
		Error();
	catch e
		printf "Computing with resultant failed\n";
		Error();
	end try;

	//if vmin ne vmax then
	//	printf "Computing valuations of %o in roots of factor %o failed (%o <= v <= %o)\n", P, F, vmin, vmax;
	//	succes := false;
	//	break;
	//end if;

	//Append(~vs, <vmin, Length(F)>);

	
end intrinsic;

intrinsic ValuationOfDerivative(P::RngUPolElt, F::FamNwtnPgonFace) -> SeqEnum[Tup]
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
		vs := ValuationOfPolynomial(t*Derivative(P) - 7*P, P, F);
		IndentPop();
		return vs;
	catch e
		printf "Error: %o\n", e`Object; IndentPop();
	end try;

	printf "Trying around 1\n";
	IndentPush();
	try
		t := Name(Parent(P),1);
		vs := ValuationOfPolynomial((t-1)*Derivative(P) - 7*P, P, F);
		IndentPop();
		return vs;
	catch e
		printf "Error: %o\n", e`Object;
		IndentPop();
	end try;

	return [];
end intrinsic;

intrinsic StructuralStability(P::RngUPolElt, F::FamNwtnPgonFace) -> BoolElt, RngIntElt
{Returns the constant mu (as a valuation) from the structural stability theorem.
Here F is the factor of P that is considered.}
	require ValuationE(LeadingCoefficient(P)) eq 0: "Argument 1 needs to be a monic polynomial:", P;

	vs := ValuationOfDerivative(P, F);

	max := -Infinity();
	for v in vs do
		max := Max(max, v[1]);
	end for;
	printf "P'(t) has valuation <= %o (valuations are %o)\n", max, vs;

	if not IsConstant(max) then
		printf "fail: precision for structural stability depends on r\n";
		return false, _;
	elif IsEmpty(vs) then
		return false, _;
	end if;

	mu := Q!max;
	v := 2*mu;
	return true, Floor(v + 1);
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
    	/*B := [Zr!b + Qpr![O(Qp!p^1) : i in [1..rank]] : b in RSpace(Integers(p^1), rank)];
    	B := [b : b in B | exists(t) {x : x in PSet | forall(i) {i : i in [1..rank] | Inside(x[i],b[i])}}];
		b := B[1];
		EvaluateParam(P, [p^r_min] cat Eltseq(b));
		ForgetParam(EvaluateParam(P, [p^r_min] cat Eltseq(b)));
		return [EtaleAlgebra(ForgetParam(EvaluateParam(P, [p^r_min] cat Eltseq(b))): W := <r_min, b>)];*/
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

intrinsic MakeMonic(P::RngUPolElt) -> RngUPolElt
{}
	p := Prime(BaseRing(BaseRing(P)));
	r := Name(BaseRing(P), 1);
	d := Degree(P);

	v := ValuationE(LeadingCoefficient(P));
	vp := Coefficient(v, 0);
	vr := Coefficient(v, 1);

	M := [Qx!(ValuationE(Coefficient(P,c))-v) / (d-c) : c in Support(P) | c ne d];
	Mp := Min(0, Floor(Min([Coefficient(m, 0) : m in M])));
	Mr := Min(0, Floor(Min([Coefficient(m, 1) : m in M])));
	return ReciprocalScale(P, p^(-Mp) * r^(-Mr)) div (p^vp * r^vr);
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

    		printf "Factor %o\n", factor; IndentPush();
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
    		IndentPop(); printf "\n";
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
