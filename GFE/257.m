Q := Rationals();

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
	Es := Etale257(p : D := D);
	Es := [<RemoveLinearFactor(E[1]), E[2]> : E in Es | ContainsLinearFactor(E[1])];

	return Es;
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
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;
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
	E2 := [<E[1], [1 + p^2 * X!B : B in E[2]]> : E in E2];

	F3 := ReciprocalPolynomial(p^7 * s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
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


intrinsic Etale257Unramified(p::RngIntElt
	: Neighbourhoods := false) -> SeqEnum
{}
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	S<x> := PolynomialRing(pAdicField(p,500));
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	Es := [];
	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(phi - a) *},Q!a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *}, p^5 * a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *}, 1 + p^2 * a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *}, p^(-7) * a>);
	end for;

	Eis := {@ E[1] : E in Es @};
	if not Neighbourhoods then
		return Eis;
	else
		return {@ <E, {@ F[2] : F in Es | F[1] eq E @}> : E in Eis @};
	end if;
end intrinsic;

intrinsic Etale257Other(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E1s := [];
	for k in [1..4] do
		F1 := SwitchVariables(Evaluate(Fs, p^k*t));
		E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
		E1 := [<E[1], [p^k * X!B : B in E[2]]> : E in E1];
		Append(~E1s, E1);
	end for;

	F2 := SwitchVariables(Evaluate(Fs, 1 + p*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, D := D);
	E2 := [<E[1], [1 + p * X!B : B in E[2]]> : E in E2];

	E3s := [];
	for k in [1..6] do
		k;
		F3 := ReciprocalPolynomial(p^k * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
		E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
		E3 := [<E[1], [Invert(p^k * X!B) : B in E[2]]> : E in E3];
		Append(~E3s, E3);
	end for;
"combining";
	Es := {@ @};
	Eis := E1s cat [E2] cat E3s;
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		"neighbourhoods";
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
end intrinsic;