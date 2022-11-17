
intrinsic Etale257Relative(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K := NumberField(p);
	require IsIsomorphic(K, QuadraticField(21)):
		"p must be a place of Q(Sqrt(21))";
	require IsFinite(p): "p must be a finite place";

	if Valuation(2, p) gt 0 then
		return Etale257Relative2(p : D := D, Neighbourhoods := Neighbourhoods);
	elif Valuation(3, p) gt 0 then
		return Etale257Relative3(p : D := D, Neighbourhoods := Neighbourhoods);
	elif Valuation(5, p) gt 0 then
		return Etale257Relative5(p : D := D, Neighbourhoods := Neighbourhoods);
	elif Valuation(7, p) gt 0 then
		return Etale257Relative7(p : D := D, Neighbourhoods := Neighbourhoods);
	else
		return Etale257RelativeUnram(p : D := D, Neighbourhoods := Neighbourhoods);
	end if; 
end intrinsic;

intrinsic Etale257Relative2(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	//TODO: take representatives of residue field here
	for a in [19] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + 2^5*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + 2^5 * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 2, Filter := Integers(2)!0, D := D);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
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


intrinsic Etale257Relative3(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
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


intrinsic Etale257Relative5(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, Filter := Integers(5)!0, D := D);

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


intrinsic Etale257Relative7(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];
	//TODO: take representatives of residue field here
	for a in [4] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + 7*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + 7 * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
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


intrinsic Etale257RelativeUnram(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];
	//TODO: take representatives of residue field here
	for a in [2..(#ResidueClassField(p)-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + pi*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + pi * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, Filter := Integers(5)!0, D := D);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 2, Filter := Integers(2)!0, D := D);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
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

