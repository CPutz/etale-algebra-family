Z := Integers();
Q := Rationals();

//Valuations of elements of a parameter space
declare type ValPrm[ValPrmElt];
declare attributes ValPrm: Values, PowerRange, Set;
declare attributes ValPrmElt: Parent, Value;

intrinsic ValuationSpace(r::<>) -> ValPrm
{Creates a valuation space}
	V := New(ValPrm);
	V`PowerRange := r;
	V`Values := cop<Parent(Infinity()), PolynomialRing(Q)>;
	V`Set := car<V`Values, V`Values>;
	return V;
end intrinsic;

intrinsic ValuationSpace(R::RngUPol, r::<>) -> ValPrm
{Creates a valuation space}
	V := New(ValPrm);
	V`PowerRange := r;
	V`Values := cop<Parent(Infinity()), R>;
	V`Set := car<V`Values, V`Values>;
	return V;
end intrinsic;

intrinsic Print(V::ValPrm)
{Print V}
	printf "The set of valuations with parameter in [%o..%o]", PowerRange(V)[1], PowerRange(V)[2]; 
end intrinsic;

intrinsic PowerRange(V::ValPrm) -> Rng
{The power range of V}
	return V`PowerRange;
end intrinsic;

intrinsic Values(V::ValPrm) -> Cop
{The structure of values a valuation can attain}
	return V`Values;
end intrinsic;

intrinsic Set(V::ValPrm) -> SetCar
{The set of valuations}
	return V`Set;
end intrinsic;

intrinsic PolynomialRing(V::ValPrm) -> RngUPol
{The polynomial ring of V}
	return Constituent(Values(V), 2);
end intrinsic;

intrinsic IsCoercible(V::ValPrm, x::.) -> BoolElt, .
{Return whether x is coercible into V and the result if so}
	if ISA(Type(x), ValPrmElt) and PowerRange(V) eq PowerRange(Parent(x)) then
		return true, ValuationSpaceElement(V, Min(x), Max(x));
	end if;
	for i in [1..#Values(V)] do
		l, c := IsCoercible(Constituent(Values(V), i), x);
		if l then
			return true, ValuationSpaceElement(V, c);
		end if;
	end for;
	l, c := IsCoercible(Set(V), x);
	if l then
		return true, ValuationSpaceElement(V, c[1], c[2]);
	end if;
	if ISA(Type(x), Tup) then
		for i in [1..#Values(V)] do
			l1, c1 := IsCoercible(Constituent(Values(V), i), x[1]);
			if l1 then
				for j in [1..#Values(V)] do
					l2, c2 := IsCoercible(Constituent(Values(V), j), x[2]);
					if l2 then
						return true, ValuationSpaceElement(V, c1, c2);
					end if;
				end for;
			end if;
		end for;
	end if;
	return false, "Coercion into S failed";
end intrinsic;

intrinsic ValuationSpaceElement(V::ValPrm, vmin::., vmax::.) -> ValPrmElt
{}
	for i in [1..#Values(V)] do
		l1, c1 := IsCoercible(Constituent(Values(V), i), vmin);
		if l1 then
			vmin := c1;
			break;
		end if;
	end for;
	for i in [1..#Values(V)] do
		l2, c2 := IsCoercible(Constituent(Values(V), i), vmax);
		if l2 then
			vmax := c2;
			break;
		end if;
	end for;
	//require ISA(Type(vmin), RngUPolElt) or ISA(Type(vmin), Infty):
	//	"Argument 2 must be an integer, univariate polynomial or +-oo";
	//require ISA(Type(vmax), RngUPolElt) or ISA(Type(vmax), Infty):
	//	"Argument 3 must be an integer, univariate polynomial or +-oo";
	v := New(ValPrmElt);
	v`Parent := V;
	v`Value := Set(V) ! <vmin, vmax>;
	return v;
end intrinsic;

intrinsic ValuationSpaceElement(V::ValPrm, r::.) -> ValPrmElt
{}
	return ValuationSpaceElement(V, r, r);
end intrinsic;

intrinsic 'eq'(v1::ValPrmElt, v2::ValPrmElt) -> BoolElt
{v1 eq v2}
	return Value(v1) eq Value(v2);
end intrinsic;

intrinsic Print(v::ValPrmElt)
{Print v}
	printf "%o", Value(v);
end intrinsic;

intrinsic Parent(v::ValPrmElt) -> ValPrm
{The Parent of v}
	return v`Parent;
end intrinsic;

intrinsic Value(v::ValPrmElt) -> SetCarElt
{The value of v}
	return v`Value;
end intrinsic;

intrinsic Max(v::ValPrmElt) -> CopElt
{The maximum value of v}
	return Value(v)[2];
end intrinsic;

intrinsic Min(v::ValPrmElt) -> CopElt
{The minimum value of v}
	return Value(v)[1];
end intrinsic;

intrinsic Max(v1::ValPrmElt, v2::ValPrmElt) -> ValPrmElt
{The maximum of v1 and v2}
	r := PowerRange(Parent(v1));
	return ValuationSpaceElement(Parent(v1),
		Min(Max(v1), Max(v2), r),
		Max(Max(v1), Max(v2), r));
end intrinsic;

intrinsic Min(v1::ValPrmElt, v2::ValPrmElt) -> ValPrmElt
{The minimum of v1 and v2}
	r := PowerRange(Parent(v1));
	return ValuationSpaceElement(Parent(v1),
		Min(Min(v1), Min(v2), r),
		Max(Min(v1), Min(v2), r));
end intrinsic;

intrinsic Max(v1::CopElt, v2::CopElt, r::<>) -> CopElt
{Maximum of a linear polynomials and +-Infinity}
	P := Parent(v1);
	m1 := Retrieve(v1);
	m2 := Retrieve(v2);
	if ISA(Type(m2), Infty) then
		if ISA(Type(m1), Infty) then
			return P ! Max(m1, m2);
		elif Sign(m2) gt 0 then
			return P ! m2;
		else
			return P ! m1;
		end if;
	else
		if ISA(Type(m1), Infty) then
			return Max(v2, v1, r);
		else
			require Degree(m1) le 1: "Argument 1 must have degree <= 1";
			require Degree(m2) le 1: "Argument 2 must have degree <= 1";
			if Coefficient(m1, 1) lt Coefficient(m2, 1) then
				Swap(~m1, ~m2);
			end if;
			f := m1 - m2;

			v := Evaluate(f, r[1]);
			if Sign(Coefficient(f,1)) * v le 0 then
				return P ! (m1 - v);
			else
				return P ! m1;
			end if;
		end if;
	end if;
end intrinsic;

intrinsic Min(v1::CopElt, v2::CopElt, r::<>) -> CopElt
{Minimum of a linear polynomials and +-Infinity}
	R := Parent(v1);
	return R!-Max(R!-v1, R!-v2, r);
end intrinsic;

intrinsic '+'(v1::ValPrmElt, v2::ValPrmElt) -> ValPrmElt
{The sum of v1 and v2}
	return ValuationSpaceElement(Parent(v1), Min(v1) + Min(v2), Max(v1) + Max(v2));
end intrinsic;

intrinsic '-'(v1::ValPrmElt) -> ValPrmElt
{The negation of v1}
	return ValuationSpaceElement(Parent(v1), -Max(v1), -Min(v1));
end intrinsic;

intrinsic '-'(v1::ValPrmElt, v2::ValPrmElt) -> ValPrmElt
{The difference of v1 and v2}
	return v1 + (-v2);
end intrinsic;

intrinsic '*'(r::RngIntElt, v::ValPrmElt) -> ValPrmElt
{The product of and integer r and v}
	if r ge 0 then
		return ValuationSpaceElement(Parent(v), r*Min(v), r*Max(v));
	else
		return ValuationSpaceElement(Parent(v), r*Max(v), r*Min(v));
	end if;
end intrinsic;

intrinsic Union(v1::ValPrmElt, v2::ValPrmElt) -> ValPrmElt
{The union of the confidence intervals v1 and v2}
	r := PowerRange(Parent(v1));
	return ValuationSpaceElement(Parent(v1),
		Min(Min(v1), Min(v2), r),
		Max(Max(v1), Max(v2), r));
end intrinsic;


//Valuations of polynomials
intrinsic Valuation(m::RngMPolElt) -> ValPrmElt
{The minimal and maximal valuation of m}
	R := Parent(m);
	Qp := BaseRing(R);
	require ISA(Type(Qp), FldPad) or
			ISA(Type(Qp), RngPad):
		"Parent of Argument 1 must be defined over a p-adic field of ring";
	require assigned Parent(m)`ParameterSet:
		"Parent of Argument 1 must be a parameter space";

	S := PolynomialRing(Q);
	range := PowerRange(R);
	V := ValuationSpace(S, range);
	C := Values(V);
	min := C ! Infinity();
	max := C ! (-Infinity());
	for s in ParameterSet(R) do
		r := Name(R, 1);
		P := UnivariatePolynomial(Evaluate(m, [r] cat TupSeq(s)));
		
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
		
		min_s := C ! (S.1 * d + vd);
		if RelativePrecision(cd) gt 0 then
			max_s := min_s;
		else
			max_s := C ! Infinity();
		end if;

		u := UniformizingElement(Qp);
		for r := range[1] to min_r-1 do
			v := C!(S!Valuation(Evaluate(P,u^r)));
			min_s := Min(min_s, v);
		end for;

		min := Min(min, min_s, range);
		max := Max(max, max_s, range);
	end for;
	return ValuationSpaceElement(V, min, max);
end intrinsic;

intrinsic ValuationE(m::RngMPolElt) -> CopElt
{Finds the valuation of m, and gives an error if it cannot determine it}
	v := Valuation(m);
	error if Max(v) ne Min(v), "Could not determine valuation of", m;
	return Max(v);
end intrinsic;

intrinsic ValuationsOfRootsPrm(P::RngUPolElt) -> SeqEnum[Tup]
{Gives the valuations of the roots of P, where P is defined
over a parameter space}
	N := FamilyOfNewtonPolygons(P);
	range := PowerRange(BaseRing(Parent(P)));
	r := range[1];
	require FamNewtonPolygonConverged(N, r):
		"Newton polygon of Argument 1 is not converged over:", range;
	V := ValuationSpace(range);
	return [<-V!Slope(F), Length(F)> : F in FacesAt(N, r)];
end intrinsic;

intrinsic ValuationsOfPolynomial(P::RngUPolElt, D::RngUPolElt) -> SeqEnum[Tup]
{Returns the valuations of P in the roots of D}
	R := BaseRing(Parent(P));
	S<c> := PolynomialRing(R);
	Rc := PolynomialRing(S);
	Pc := Rc ! Coefficients(P);
	Dc := Rc ! Coefficients(D);

	T := PolynomialRing(PolynomialRing(PolynomialRing(Z,Rank(R))));
	res := S!Resultant(T!(c - Pc), T!Dc);

	return ValuationsOfRootsPrm(res);
end intrinsic;

intrinsic ValuationsOfPolynomial(P::RngUPolElt, D::RngUPolElt, F::FamNwtnPgonFace) -> Tup
{Returns the valuations of P in the roots of a factor F of D}
	range := PowerRange(BaseRing(Parent(D)));
	V := ValuationSpace(range);
	v := V!<-Infinity(),Infinity()>;
	vF := -Slope(F);
	
	P;
	F;

	for m in Support(P) do
		vm := Valuation(Coefficient(P, m));
		v := Min(v, vm + V!(m * vF));

		m;
		vm;
		V!(m * vF);
		v;
	end for;

	return <v, Length(F)>;
end intrinsic;