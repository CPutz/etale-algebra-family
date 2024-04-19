intrinsic EtaleAlgebras357(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{Returns the isomorphism classes of etale algebras over Q_p attached to the GFE
with signature (2,5,7) and Belyi map 15t^7 - 35t^6 + 21t^5. If Neighbourhoods is
set to true then all etale algebras will contain meta data containing to the
p-adic neighbourhoods such that evaluating at these parameter values will yield
the corresponding etale algebra.}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	Par1 := pAdicNbhdSpace(Rationals(), p : MinVal := 5, CongrVal := Integers(5)!0);
	E1 := EtaleAlgebraFamily(F, p : ParameterSpace := Par1, Precision := 700);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	Par2 := pAdicNbhdSpace(Rationals(), p : MinVal := 3, CongrVal := Integers(3)!0);
	E2 := EtaleAlgebraFamily(F2, p : ParameterSpace := Par2, Precision := 500);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
	Par3 := pAdicNbhdSpace(Rationals(), p : MinVal := 7, CongrVal := Integers(7)!0);
	E3 := EtaleAlgebraFamily(F3, p : ParameterSpace := Par3, Precision := 500);
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

	return [SimplifyToProduct(E : D := D) : E in Es];
end intrinsic;

intrinsic EtaleAlgebras357CoeffRamification(p::RngIntElt, a::RngIntElt, b::RngIntElt, c::RngIntElt
	: Precision := 500) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;

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
			E0 := EtaleAlgebraFamily(F0, p);
			Append(~E0s, E0);
		end for;
	end if;

	if vabc eq 0 or va gt 0 then
		minvalx := va eq 0 select 5 else va;
		Par1 := pAdicNbhdSpace(Rationals(), p : MinVal := minvalx, CongrVal := Integers(5)!va);
		E1 := EtaleAlgebraFamily(F, p :Precision := Precision,
			CalcIso := false, ParameterSpace := Par1);
	end if;

	if vabc eq 0 or vb gt 0 then
		minvaly := vb eq 0 select 3 else vb;
		F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
		Par2 := pAdicNbhdSpace(Rationals(), p : MinVal := minvaly, CongrVal := Integers(3)!vb);
		E2 := EtaleAlgebraFamily(F2, p : Precision := Precision,
			CalcIso := false, ParameterSpace := Par2);
	end if;

	if vabc eq 0 or vc gt 0 then
		minvalz := vc eq 0 select 7 else vc;
		F3 := ReciprocalPolynomial(s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
		Par3 := pAdicNbhdSpace(Rationals(), p : MinVal := minvalz, CongrVal := Integers(7)!vc);
		E3 := EtaleAlgebraFamily(F3, p : Precision := Precision,
			CalcIso := false, ParameterSpace := Par3);
	end if;

	Eis := (&cat E0s) cat E1 cat E2 cat E3;
	return Eis;
end intrinsic;