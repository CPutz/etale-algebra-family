Q := Rationals();
Z := Integers();

intrinsic EtaleAlgebras257(p::RngIntElt
	: Database := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Simplify := true) -> SeqEnum
{Returns the isomorphism classes of etale algebras over Q_p attached to the GFE
with signature (2,5,7) and Belyi map of degree 8. If Neighbourhoods is set to
true then all etale algebras will contain meta data containing to the p-adic
neighbourhoods such that evaluating at these parameter values will yield the
corresponding etale algebra. If Simplify is set to true then SimplifyToProduct
will be applied to all etale algebras in the result.}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);

	if Simplify and p eq 2 and <2,8> notin Precomputed(Database) then
		printf "Warning: database of local fields provided does not contain a precomputed list of degree 8 extensions of Q_2. ";
		printf "This may lead to a very long running time.\n";
		printf "Solution: either set Simplify := false or Database := LocalFieldDatabaseOctic2Adics().\n";
	end if;

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := Database);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	Par1 := pAdicNbhdSpace(Rationals(), p : MinVal := 5, CongrVal := Integers(5)!0);
	E1 := EtaleAlgebraFamily(F, p : D := Database, Precision := 400,
		ParameterSpace := Par1);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	Par2 := pAdicNbhdSpace(Rationals(), p : MinVal := 2, CongrVal := Integers(2)!0);
	E2 := EtaleAlgebraFamily(F2, p : D := Database, Precision := 400,
		ParameterSpace := Par2);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	Par3 := pAdicNbhdSpace(Rationals(), p : MinVal := 7, CongrVal := Integers(7)!0);
	E3 := EtaleAlgebraFamily(F3, p : D := Database, Precision := 400,
		ParameterSpace := Par3);
	for i := 1 to #E3 do
		SetData(~E3[i], [Invert(B) : B in Data(E3[i])]);
	end for;

	Es := [];
	Eis := (&cat E0s) cat E1 cat E2 cat E3;
	if not Neighbourhoods then
		for i := 1 to #Eis do
			ClearData(~Eis[i]);
		end for;
	end if;

	for Ei in Eis do
		if exists (i) {i : i in [1..#Es] | IsIsomorphic(Es[i], Ei)} then
			if Neighbourhoods then
				AddData(~Es[i], Data(Ei));
			end if;
		else
			Append(~Es, Ei);
		end if;
	end for;

	if Simplify then
		return [SimplifyToProduct(E : D := Database) : E in Es];
	else
		return Es;
	end if;
end intrinsic;

intrinsic EtaleAlgebras257Unramified(p::RngIntElt) -> SeqEnum
{Computes the result of EtaleAlgebras257 for primes not equal to 2, 5 or 7 in a
more efficient way.}
	require p notin [2,5,7]: "Argument 1 must be unequal to 2, 5 or 7";
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	Qp := pAdicField(p,20);
	S<x> := PolynomialRing(Qp);
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	Es := {@ @};
	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *});
	end for;

	return [EtaleAlgebra([UnramifiedExtension(Qp,C) : C in E], Qp) : E in Es];
end intrinsic;


intrinsic EtaleAlgebras257Unramified2(p::RngIntElt) -> SeqEnum
{Computes the result of EtaleAlgebras257 for primes not equal to 2, 5 or 7 in a
more efficient way.}
	require p notin [2,5,7]: "Argument 1 must be unequal to 2, 5 or 7";
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	Qp := pAdicField(p,20);
	S<x> := PolynomialRing(Qp);
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	Es := {@ @};
	for a in [2..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *}, Q!a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *}, Q!p^5 * a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *}, Q!1 + p^2 * a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *}, p^(-7) * a>);
	end for;

	vals := {@ E[1] : E in Es @};
	return [<v, [E[2] : E in Es | E[1] eq v]> : v in vals];
end intrinsic;

intrinsic EtaleAlgebras257CoeffRamification(p::RngIntElt, a::RngIntElt, b::RngIntElt, c::RngIntElt
	: Precision := 500) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);

	va := Valuation(a,p);
	vb := Valuation(b,p);
	vc := Valuation(c,p);
	vabc := Valuation(a*b*c,p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	if vabc eq 0 then
		for a in [2..(p-1)] do
			F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
			E0 := EtaleAlgebraFamily(F0, p : Precision := Precision, CalcIso := false);
			Append(~E0s, E0);
		end for;
	end if;

	if vabc eq 0 or va gt 0 then
		minvalx := va eq 0 select 5 else va;
		Par1 := pAdicNbhdSpace(Rationals(), p : MinVal := minvalx, CongrVal := Integers(5)!va);
		E1 := EtaleAlgebraFamily(F, p : Precision := Precision,
			CalcIso := false, ParameterSpace := Par1);
	end if;

	if vabc eq 0 or vb gt 0 then
		minvaly := vb eq 0 select 2 else vb;
		F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
		Par2 := pAdicNbhdSpace(Rationals(), p : MinVal := minvaly, CongrVal := Integers(2)!vb);
		E2 := EtaleAlgebraFamily(F2, p : Precision := Precision,
			CalcIso := false, ParameterSpace := Par2);
	end if;

	if vabc eq 0 or vc gt 0 then
		minvalz := vc eq 0 select 7 else vc;
		psi := s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1);
		if p eq 5 then
			if vc ge 5 then
				psi := s * 5^(minvalz - 5) * 4*t^5*(t^3 + 4*t^2 + 14*t + 70) - (4*t - 5);
				minvalz := 0;
			else //vc lt 5
				psi := s * 5^(minvalz + 7 - 5) * 4*t^5*(t^3 + 4*t^2 + 14*t + 70) - (4*t - 5);
				minvalz := 0;
			end if;
		end if;

		F3 := ReciprocalPolynomial(psi);
		Par3 := pAdicNbhdSpace(Rationals(), p : MinVal := minvalz, CongrVal := Integers(7)!vc);
		E3 := EtaleAlgebraFamily(F3, p : Precision := Precision,
			CalcIso := false, ParameterSpace := Par3);

		//the remaining cases for p=5 and 0 < v_3(c) < 5
		if p eq 5 and vc lt 5 and vc ne 0 then
			for a in [1..4] do
				F3a := 5^vc * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (a + 5*s) * (4*t - 1);
				E3a := EtaleAlgebraFamily(F3a, p : Precision := Precision, CalcIso := false, BoundMethod := "Difference");
				E3 cat:= E3a;
			end for;
		end if;
	end if;

	Eis := (&cat E0s) cat E1 cat E2 cat E3;
	return Eis;
end intrinsic;