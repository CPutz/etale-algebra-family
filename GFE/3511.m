Q := Rationals();

intrinsic EtaleAlgebras3511(p::RngIntElt
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

	/*if p eq 5 then
		psi := -s * 5^11 * t * (33 + 11*t + 3*t^2)^5 - 5^10;
		minvalz := 0;
	else
		minvalz := 11;
	end if;*/

	E0s := [];
	for a in [2..(p-1)] do
		F0 := phi - (a + p*s);
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	Par1 := pAdicNbhdSpace(Rationals(), p : MinVal := 5, CongrVal := Integers(5)!0);
	E1 := EtaleAlgebraFamily(phi - s, p : ParameterSpace := Par1, D := D);

	Par2 := pAdicNbhdSpace(Rationals(), p : MinVal := 3, CongrVal := Integers(3)!0);
	E2 := EtaleAlgebraFamily(phi - (1 + s), p : ParameterSpace := Par2, D := D);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(psi);
	Par3 := pAdicNbhdSpace(Rationals(), p : MinVal := 11, CongrVal := Integers(11)!0);
	E3 := EtaleAlgebraFamily(F3, p :ParameterSpace := Par3, D := D);
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


intrinsic EtaleAlgebras3511Coeff(p::RngIntElt, a::RngIntElt, b::RngIntElt, c::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * t * (33 + 11*t + 3*t^2)^5 - 5^10;

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
			F0 := phi - (a + p*s);
			E0 := EtaleAlgebraFamily(F0, p : D := D, BoundMethod := "Difference");
			for i := 1 to #E0 do
				SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
			end for;
			Append(~E0s, E0);
		end for;
	end if;

	if vabc eq 0 or va gt 0 then
		minvalx := va eq 0 select 5 else va;
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvalx, CongrVal := Integers(5)!va);
		if p eq 11 then
			prec := 3000;
		else
			prec := 1000;
		end if;
		E1 := EtaleAlgebraFamily(phi - s, p : ParameterSpace := Par, D := D, Precision := prec, BoundMethod := "Difference");
	end if;

	if vabc eq 0 or vb gt 0 then
		minvaly := vb eq 0 select 3 else vb;
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvaly, CongrVal := Integers(3)!vb);
		E2 := EtaleAlgebraFamily(phi - (1 + s), p : ParameterSpace := Par, D := D, Precision := 1000, BoundMethod := "Difference");
		for i := 1 to #E2 do
			SetData(~E2[i], [1 + B : B in Data(E2[i])]);
		end for;
	end if;

	if vabc eq 0 or vc gt 0 then
		minvalz := vc eq 0 select 11 else vc;
		//divide out a factor of 5^10 if possible for efficiency
		if p eq 5 and minvalz ge 10 then
			psi := -s * 5^(minvalz - 10) * t * (33 + 11*t + 3*t^2)^5 - 1;
			minvalz := 0;
		end if;
		if p eq 3 then
			psi := -s * 3^minvalz * t * (99 + 11*t + t^2)^5 - 3^6 * 5^10;
			minvalz := 0;
		end if;

		F3 := ReciprocalPolynomial(psi);
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvalz, CongrVal := Integers(11)!minvalz);
		E3 := EtaleAlgebraFamily(F3, p : ParameterSpace := Par, D := D, Precision := 1000, BoundMethod := "Difference");
		for i := 1 to #E3 do
			SetData(~E3[i], [Invert(B) : B in Data(E3[i])]);
		end for;
	end if;

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

intrinsic EtaleAlgebras3511CoeffRamification(p::RngIntElt, a::RngIntElt, b::RngIntElt, c::RngIntElt
	: D := LocalFieldDatabase(),
	  Precision := 500) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * t * (33 + 11*t + 3*t^2)^5 - 5^10;

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
			F0 := phi - (a + p*s);
			E0 := EtaleAlgebraFamily(F0, p : D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");
			Append(~E0s, E0);
		end for;
	end if;

	if vabc eq 0 or va gt 0 then
		minvalx := va eq 0 select 5 else va;
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvalx, CongrVal := Integers(5)!va);
		E1 := EtaleAlgebraFamily(phi - s, p : ParameterSpace := Par, D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");
	end if;

	if vabc eq 0 or vb gt 0 then
		minvaly := vb eq 0 select 3 else vb;
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvaly, CongrVal := Integers(3)!vb);
		E2 := EtaleAlgebraFamily(phi - (1 + s), p : ParameterSpace := Par, D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");
	end if;

	if vabc eq 0 or vc gt 0 then
		minvalz := vc eq 0 select 11 else vc;
		//divide out a factor of 5^10 if possible for efficiency
		if p eq 5 then
			if minvalz ge 10 then
				psi := -s * 5^(minvalz - 10) * t * (33 + 11*t + 3*t^2)^5 - 1;
				minvalz := 0;
			else // vc lt 10
				//first for 5^(vc+11)
				psi := -s * 5^(minvalz + 11 - 10) * t * (33 + 11*t + 3*t^2)^5 - 1;
				minvalz := 0;
			end if;
		end if;
		if p eq 3 then
			if minvalz ge 6 then
				psi := -s * 3^(minvalz - 6) * t * (99 + 11*t + t^2)^5 - 5^10;
				minvalz := 0;
			else // vc lt 6
				psi := -s * 3^(minvalz + 11 - 6) * t * (99 + 11*t + t^2)^5 - 5^10;
				minvalz := 0;
			end if;
		end if;

		F3 := ReciprocalPolynomial(psi);
		Par := pAdicNbhdSpace(Rationals(), p : MinVal := minvalz, CongrVal := Integers(11)!minvalz);
		E3 := EtaleAlgebraFamily(F3, p : ParameterSpace := Par, D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");

		//the remaining cases for p=3 and 0 < v_3(c) < 6
		if p eq 3 and vc lt 6 and vc ne 0 then
			for a in [1..2] do
				F3a := -t * 3^vc * (33 + 11*t + 3*t^2)^5 - 5^10 * (a + 3*s);
				E3a := EtaleAlgebraFamily(F3a, p : D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");
				E3 cat:= E3a;
			end for;
		end if;

		//the remaining cases for p=5 and 0 < v_5(c) < 10
		if p eq 5 and vc lt 10 and vc ne 0 then
			for a in [1..4] do
				F3a := -t * (33 + 11*t + 3*t^2)^5 - 5^(10 - vc) * (a + 5*s);
				E3a := EtaleAlgebraFamily(F3a, p : D := D, Precision := Precision, CalcIso := false, BoundMethod := "Difference");
				E3 cat:= E3a;
			end for;
		end if;
	end if;

	Eis := (&cat E0s) cat E1 cat E2 cat E3;
	return Eis;
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