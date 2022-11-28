
intrinsic Etale257Relative(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{}
	K := NumberField(p);
	require IsIsomorphic(K, QuadraticField(21)):
		"p must be a place of Q(Sqrt(21))";
	require IsFinite(p): "p must be a finite place";

	if Valuation(2, p) gt 0 then
		return Etale257Relative2(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(3, p) gt 0 then
		return Etale257Relative3(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(5, p) gt 0 then
		return Etale257Relative5(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(7, p) gt 0 then
		return Etale257Relative7(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	else
		return Etale257RelativeUnram(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	end if; 
end intrinsic;

intrinsic Etale257Relative2(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
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
		E0 := EtaleAlgebraFamily(F0, p : D := D, Hint := Hint);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + 2^5 * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 2, CongrVal := Integers(2)!0, D := D, Hint := Hint);
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
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);
	e := Valuation(3, p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := e*7, CongrVal := Integers(e*7)!0, D := D, Hint := Hint);
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
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
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

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, CongrVal := Integers(5)!0, D := D, Hint := Hint);

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
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);
	e := Valuation(7, p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];
	//TODO: take representatives of residue field here
	for a in [4] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + 7*t));
		E0 := EtaleAlgebraFamily(F0, p : MinVal := 2, CongrVal := Integers(e)!0, D := D, Hint := Hint);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + 7 * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := e*7, CongrVal := Integers(e*7)!0, D := D, Hint := Hint);
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
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);
	//TODO: p cannot lie above 2,3,5,7

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];
	//TODO: take representatives of residue field here
	for a in [2..(#ResidueClassField(p)-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + pi*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D, Hint := Hint);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + pi * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, CongrVal := Integers(5)!0, D := D, Hint := Hint);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 2, CongrVal := Integers(2)!0, D := D, Hint := Hint);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := 7, CongrVal := Integers(7)!0, D := D, Hint := Hint);
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

