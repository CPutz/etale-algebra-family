Q := Rationals();

/*intrinsic Etale3511(p::RngIntElt
	: D := LocalFieldDatabase()) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * p^11 * t * (33 + 11*t + 3*t^2)^5 - 5^10;

	if p eq 3 then
		psi := Evaluate(psi, t/3);
	end if;

	//Qnf := RationalsAsNumberField();
	//pl := Decomposition(Qnf, p)[1,1];
	//K := ChangePrecision(Completion(Qnf, pl), 500);
	//K := pAdicField(p, 500);
	//X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := phi - (a + p*s);
		E0 := EtaleAlgebraFamily3(F0, p : D := D);
		//E0 := [<E[1], [a + p * B : B in E[2]]> : E in E0];
		E0 := [E[1] : E in E0];
		
		Append(~E0s, E0);
	end for;

	F1 := phi - p^5*s;
	E1 := EtaleAlgebraFamily3(F1, p : Filter := Integers(5)!0, D := D);
	//E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];
	E1 := [E[1] : E in E1];

	F2 := phi - (1 + p^3*s);
	E2 := EtaleAlgebraFamily3(F2, p : Filter := Integers(3)!0, D := D);
	//E2 := [<E[1], [1 + p^3 * X!B : B in E[2]]> : E in E2];
	E2 := [E[1] : E in E2];

	F3 := ReciprocalPolynomial(psi);
	E3 := EtaleAlgebraFamily3(F3, p : Filter := Integers(11)!0, D := D);
	//E3 := [<E[1], [Invert(p^11 * X!B) : B in E[2]]> : E in E3];
	E3 := [E[1] : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E);
		end for;
	end for;

	//EBs := {@ @};
	//if Neighbourhoods then
	//	for E in Es do
	//		Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
	//	end for;
	//	Es := EBs;
	//end if;

	return SetToSequence(Es);
end intrinsic;*/

intrinsic Etale3511(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * t * (33 + 11*t + 3*t^2)^5 - 5^10;

	if p eq 3 then
		psi := Evaluate(psi, t/3);
	end if;

	if p eq 5 then
		psi := -s * 5^11 * t * (33 + 11*t + 3*t^2)^5 - 5^10;
		minvalz := 0;
	else
		minvalz := 11;
	end if;

	E0s := [];
	for a in [2..(p-1)] do
		F0 := phi - (a + p*s);
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(phi - s, p : MinVal := 5, Filter := Integers(5)!0, D := D);

	E2 := EtaleAlgebraFamily(phi - (1 + s), p : MinVal := 3, Filter := Integers(3)!0, D := D);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(psi);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := minvalz, Filter := Integers(11)!0, D := D);
	for i := 1 to #E3 do
		SetData(~E3[i], [Invert(B) : B in Data(E3[i])]);
	end for;
E0s;
E1;
E2;
E3;


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

/*intrinsic Etale3511Unramified(p::RngIntElt) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * p^11 * t * (33 + 11*t + 3*t^2)^5 - 5^10;

	Es := {@ @};
	for a in [2..(p-1)] do
		for E in EtaleAlgebraFamily3(phi - (a + p*s), p) do
			Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
		end for;
	end for;

	for E in EtaleAlgebraFamily3(phi - p^5*s, p : Filter := Integers(5)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	for E in EtaleAlgebraFamily3(phi - (1 + p^3*s), p : Filter := Integers(3)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	for E in EtaleAlgebraFamily3(ReciprocalPolynomial(psi), p : Filter := Integers(11)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	return Es;
end intrinsic;*/