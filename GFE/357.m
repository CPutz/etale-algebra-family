intrinsic Etale357(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{Computes the isomorphism classes of local etale algebras at p attached to
the GFE with signature (3,5,7) and Belyi map 15t^7 - 35t^6 + 21t^5.}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, Filter := Integers(5)!0, D := D);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 3, Filter := Integers(3)!0, D := D);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := 7, Filter := Integers(7)!0, D := D);
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

	return Es;
end intrinsic;