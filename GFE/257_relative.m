
intrinsic EtaleAlgebras257Relative(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Returns the isomorphism classes of etale algebras over Q(Sqrt(21))_p attached
to the GFE with signature (2,5,7) and Belyi map of degree 7 over Q(Sqrt(21)).
If Neighbourhoods is set to true then all etale algebras will contain meta data
containing to the p-adic neighbourhoods such that evaluating at these parameter
values will yield the corresponding etale algebra.}
	K := NumberField(p);
	require IsIsomorphic(K, QuadraticField(21)):
		"p must be a place of Q(Sqrt(21))";
	require IsFinite(p): "p must be a finite place";

	if Valuation(2, p) gt 0 then
		return EtaleAlgebras257Relative2(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(3, p) gt 0 then
		return EtaleAlgebras257Relative3(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(5, p) gt 0 then
		return EtaleAlgebras257Relative5(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	elif Valuation(7, p) gt 0 then
		return EtaleAlgebras257Relative7(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	else
		return EtaleAlgebras257RelativeUnramified(p : D := D,
			Neighbourhoods := Neighbourhoods, Hint := Hint);
	end if; 
end intrinsic;

intrinsic EtaleAlgebras257Relative2(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Performs the calculations for EtaleAlgebras257Relative for the prime of
Q(Sqrt(21)) above 2.}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p :
		MinVal := 2, CongrVal := Integers(2)!0, Hint := Hint, Precision := 500);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(2^7 * (1 + 2*s) * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : Hint := Hint, Precision := 500);
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


intrinsic EtaleAlgebras257Relative3(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Performs the calculations for EtaleAlgebras257Relative for the prime of
Q(Sqrt(21)) above 3.}
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
	E3 := EtaleAlgebraFamily(F3, p : MinVal := e*7, CongrVal := Integers(e*7)!0,
		Hint := Hint, Precision := 500);
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


intrinsic EtaleAlgebras257Relative5(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Performs the calculations for EtaleAlgebras257Relative for the primes of
Q(Sqrt(21)) above 5.}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, CongrVal := Integers(5)!0,
		Hint := Hint, Precision := 500);

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


intrinsic EtaleAlgebras257Relative7(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Performs the calculations for EtaleAlgebras257Relative for the prime of
Q(Sqrt(21)) above 7.}
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

	for a in [4] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + 7*t));
		E0 := EtaleAlgebraFamily(F0, p : MinVal := 2, CongrVal := Integers(e)!0, Hint := Hint);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + 7 * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := e*7, CongrVal := Integers(e*7)!0,
		Hint := Hint, Precision := 500);
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


intrinsic EtaleAlgebras257RelativeUnramified(p::PlcNumElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Hint := []) -> SeqEnum
{Performs the calculations for EtaleAlgebras257Relative for the finite primes of
Q(Sqrt(21)) not above 2, 3, 5 or 7.}
	K<a> := NumberField(p);
	S<s> := PolynomialRing(K);
	R<t> := PolynomialRing(S);
	F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9 * s;

	pi := UniformizingElement(p);

	E0s := [];
	E1 := [];
	E2 := [];
	E3 := [];

	R,m := ResidueClassField(Ideal(p));
	for a in [K!(x@@m) : x in R | x ne 0 and x ne 1] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + pi*t));
		E0 := EtaleAlgebraFamily(F0, p : Hint := Hint);

		//Precision := 50;
		//Kp,phi := Completion(K,p : Precision := Precision);
		//OKp := Integers(Kp);
		//piKp := UniformizingElement(Kp);
		//OKpq := quo<OKp | piKp^Precision>;
		//for i := 1 to #E0 do
			//SetData(~E0[i], [OKpq!phi(a) + OKpq!phi(pi) * B where X := Parent(B) : B in Data(E0[i])]);
		//end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p : MinVal := 5, CongrVal := Integers(5)!0,
		Hint := Hint, Precision := 500);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p : MinVal := 2, CongrVal := Integers(2)!0,
		Hint := Hint, Precision := 500);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) - 9);
	E3 := EtaleAlgebraFamily(F3, p : MinVal := 7, CongrVal := Integers(7)!0,
		Hint := Hint, Precision := 500);
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

