intrinsic Etale257(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
		Append(~E0s, E0);
	end for;

	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];

	F2 := SwitchVariables(Evaluate(Fs, 1 + p^2*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, D := D);
	E2 := [<E[1], [1 + p^2 * X!B : B in E[2]]> : E in E2];

	F3 := ReciprocalPolynomial(p^7 * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
	E3 := [<E[1], [Invert(p^7 * X!B) : B in E[2]]> : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
end intrinsic;

intrinsic Etale257Linear(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	E0s, E1, E2, E3 := Etale257(p : D := D);

	E0s := [[<RemoveLinearFactor(E[1]), E[2]> : E in E0 | ContainsLinearFactor(E[1])] : E0 in E0s];
	E1 := [<RemoveLinearFactor(E[1]), E[2]> : E in E1 | ContainsLinearFactor(E[1])];
	E2 := [<RemoveLinearFactor(E[1]), E[2]> : E in E2 | ContainsLinearFactor(E[1])];
	E3 := [<RemoveLinearFactor(E[1]), E[2]> : E in E3 | ContainsLinearFactor(E[1])];

	return E0s, E1, E2, E3;
end intrinsic;

intrinsic ContainsLinearFactor(E::EtAlg) -> BoolElt
{Returns true if E contains a linear factor}
	return HasRoot(DefiningPolynomial(E));
end intrinsic;

intrinsic RemoveLinearFactor(E::EtAlg) -> EtAlg
{Provided an etale algebra E with a linear factor, remove it}
	Cs := Components(E);
	Csnew := [];
	for C in Cs do
		if AbsoluteDegree(C[1]) eq 1 then
			if C[2] gt 1 then
				Append(~Csnew, <C[1], C[2]-1>);
			end if;
		else
			Append(~Csnew, C);
		end if;
	end for;
	return EtaleAlgebra(Csnew);
end intrinsic;

intrinsic Etale257_2(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	printf "S3\n";
	//F3 := ReciprocalPolynomial(p^7 * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	F3 := p^7 * 4*t^5*(25*t^3 + 20*s*t^2 + 14*s^2*t + 14*s^3) - s^7*(4*t - 1);
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);

	return E3;
end intrinsic;


intrinsic Etale357(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;
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
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	printf "\n";

	printf "S2\n";
	F2 := SwitchVariables(Evaluate(Fs, 1 + p^3*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(3)!0, D := D);
	printf "\n";

	printf "S3\n";
	F3 := ReciprocalPolynomial(p^7 * s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);

	return E0s, E1, E2, E3;
end intrinsic;





intrinsic Etale3511(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := (3*t^2 + t + 1)^5 * (1 - 5*t) - s;
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
		Append(~E0s, E0);
	end for;

	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];

	F2 := SwitchVariables(Evaluate(Fs, 1 + p^3*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(3)!0, D := D);
	E2 := [<E[1], [1 + p^3 * X!B : B in E[2]]> : E in E2];

	F3 := (243 + 4455*t + 46035*t^2 + 315810*t^3 + 1591755*t^4 + 
 6030761*t^5 + 17509305*t^6 + 38213010*t^7 + 61272585*t^8 + 
 65225655*t^9 + 39135393*t^10) * p^11 * s + 9765625*t^11;
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(11)!0, D := D);
	E3 := [<E[1], [Invert(p^11 * X!B) : B in E[2]]> : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
end intrinsic;
