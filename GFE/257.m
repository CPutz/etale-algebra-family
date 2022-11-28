Q := Rationals();
Z := Integers();

intrinsic EtaleAlgebras257(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{Returns the etale algebras over Q_p attached to the GFE with signature (2,5,7)
and Belyi map of degree 8. If Neighbourhoods is set to true then all etale
algebras will contain meta data containing to the p-adic neighbourhoods such
that evaluating at these parameter values will yield the corresponding etale
algebra.}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p :
		MinVal := 5, CongrVal := Integers(5)!0, D := D, Precision := 400);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p :
		MinVal := 2, CongrVal := Integers(2)!0, D := D, Precision := 400);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	E3 := EtaleAlgebraFamily(F3, p :
		MinVal := 7, CongrVal := Integers(7)!0, D := D, Precision := 400);
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

	return [SimplifyToProduct(E) : E in Es];
end intrinsic;

intrinsic EtaleAlgebras257Unramified(p::RngIntElt) -> SeqEnum
{Computes the result of EtaleAlgebras257 for primes not equal to 2, 5 or 7 in a
more efficient way.}
	require p notin [2,5,7]: "Argument 1 must be unequal to 2, 5 or 7";
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	Qp := pAdicField(p,20);
	S<x> := PolynomialRing(Qp);
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	Es := {@ @};
	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *});
	end for;

	for a in [2..(p-1)] do
		Include(~Es, {* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *});
	end for;

	return [EtaleAlgebra([<UnramifiedExtension(Qp,C),1> : C in E]) : E in Es];
end intrinsic;
