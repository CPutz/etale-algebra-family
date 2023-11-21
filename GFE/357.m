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

	E1 := EtaleAlgebraFamily(F, p :
		MinVal := 5, CongrVal := Integers(5)!0, Precision := 700);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p :
		MinVal := 3, CongrVal := Integers(3)!0, Precision := 500);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
	E3 := EtaleAlgebraFamily(F3, p :
		MinVal := 7, CongrVal := Integers(7)!0, Precision := 500);
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