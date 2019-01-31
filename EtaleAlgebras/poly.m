//Constants
Z := Integers();
Q := Rationals();
Zx := PolynomialRing(Z);
Qx := PolynomialRing(Q);

//Add attributes to multivariate polynomial rings which
//we use to represent our families of etale algebras
declare attributes RngMPol: PowerRange, ParameterSet;

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
		"Argument 1 depends on a variable of its base ring";
	return S ! [ConstantCoefficient(c) : c in Coefficients(P)];
end intrinsic;

intrinsic ReciprocalScale(P::RngUPolElt, r::RngElt) -> RngUPolElt
{Scales the coefficients of P by r with reverse weights}
	d := Degree(P);
	return Parent(P) ! [r^(d-c) * Coefficient(P, c) : c in [0..d]]; 
end intrinsic;

intrinsic MakeMonic(P::RngUPolElt) -> RngUPolElt
{Transforms P such that it is becomes monic}
	p := Prime(BaseRing(BaseRing(P)));
	r := Name(BaseRing(P), 1);
	d := Degree(P);

	v := ValuationE(LeadingCoefficient(P));
	vp := Z!Coefficient(v, 0);
	vr := Z!Coefficient(v, 1);

	M := [Qx!(ValuationE(Coefficient(P,c))-v) / (d-c) : c in Support(P) | c ne d];
	Mp := Min(0, Floor(Min([Coefficient(m, 0) : m in M])));
	Mr := Min(0, Floor(Min([Coefficient(m, 1) : m in M])));
	return ReciprocalScale(P, p^(-Mp) * r^(-Mr)) div (p^vp * r^vr);
end intrinsic;

intrinsic MakeMonicIntegral(P::RngUPolElt) -> RngUPolElt
{Scales a polynomial over a local field such that it is monic and
integral}
	//TODO: ASSERT: Must be over a local field
	K := BaseRing(P);
	p := Prime(K);
	c := Valuation(LeadingCoefficient(P));
	P /:= p^c;
	//TODO: Can me more optimized
	v := Min([Valuation(a) : a in Coefficients(P)]);
	return ScaleCoefficients(P, K!p^(-v));
end intrinsic;