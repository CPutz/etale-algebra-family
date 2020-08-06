intrinsic Etale257(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	E0s := [];
	for a in [2..(p-1)] do
		printf "S0: a = %o\n", a;
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		Append(~E0s, E0);
		printf "\n";
	end for;
	
	printf "S1\n";
	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, Precision := 500, D := D);
	printf "\n";

	printf "S2\n";
	F2 := SwitchVariables(Evaluate(Fs, 1 + p^2*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, Precision := 1000, D := D);
	printf "\n";

	return E0s, E1, E2;
end intrinsic;