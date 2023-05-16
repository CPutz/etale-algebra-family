Q := Rationals();
Z := Integers();

intrinsic EtaleAlgebras257(p::RngIntElt
	: Database := LocalFieldDatabase(),
	  Neighbourhoods := false,
	  Simplify := true) -> SeqEnum
{Returns the isomorphism classes of etale algebras over Q_p attached to the GFE
with signature (2,5,7) and Belyi map of degree 8. If Neighbourhoods is set to
true then all etale algebras will contain meta data containing to the p-adic
neighbourhoods such that evaluating at these parameter values will yield the
corresponding etale algebra. If Simplify is set to true then SimplifyToProduct
will be applied to all etale algebras in the result.}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := Database);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p :
		MinVal := 5, CongrVal := Integers(5)!0, D := Database, Precision := 400);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p :
		MinVal := 2, CongrVal := Integers(2)!0, D := Database, Precision := 400);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	E3 := EtaleAlgebraFamily(F3, p :
		MinVal := 7, CongrVal := Integers(7)!0, D := Database, Precision := 400);
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

	if Simplify and <2,8> notin Precomputed(Database) then
		printf "Warning: database of local fields provided does not contain a precomputed list of degree 8 extensions of Q_2. ";
		printf "This may lead to a very long running time.\n";
		printf "Solution: either set Simplify = false or Database = LocalFieldDatabaseOctic2Adics().\n";
	end if;

	if Simplify then
		return [SimplifyToProduct(E : D := Database) : E in Es];
	else
		return Es;
	end if;
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

	return [EtaleAlgebra([UnramifiedExtension(Qp,C) : C in E], Qp) : E in Es];
end intrinsic;


intrinsic EtaleAlgebras257Unramified2(p::RngIntElt) -> SeqEnum
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
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *}, Q!a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *}, Q!p^5 * a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *}, Q!1 + p^2 * a>);
	end for;

	for a in [1..(p-1)] do
		Include(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *}, p^(-7) * a>);
	end for;

	vals := {@ E[1] : E in Es @};
	return [<v, [E[2] : E in Es | E[1] eq v]> : v in vals];
end intrinsic;


function myheight(x);
	m := Max([Abs(c) : c in Eltseq(x)]);
	//m := Sqrt(&+[Abs(Evaluate(x,p))^2 : p in InfinitePlaces(Parent(x))]);
	return m;
end function;

function myheight2(p);
	return Max([myheight(c) : c in Eltseq(p)]);
end function;

intrinsic CoprimeRepresentative(coords::SeqEnum) -> SeqEnum
{}
	K<a> := Parent(coords[1]);
	denom := LCM([Denominator(Norm(c)) : c in coords]);
	num := GCD([Numerator(Norm(c)) : c in coords]);
	coords_new := coords;
	"start factoring";
	for p in Factorization(denom * num) do
		"end factoring";
		for P in Decomposition(K,p[1]) do
			val := Min([Valuation(c,P[1]) : c in coords]);
			if val ne 0 then
				_,g := IsPrincipal(Ideal(P[1]));
				coords_new := [g^(-val) * c : c in coords_new];
			end if;
		end for;
	end for;

	//preferred representatives of OK*/(OK*)^2
	u1 := -1;
	u2 := a^5 + a^4 - a^3 - 2*a^2 - a - 1;
	u3 := -8*a^6 - 17*a^5 - 14*a^4 + 5*a^3 + 30*a^2 + 39*a + 14;
	u4 := -a^6 + 4*a^5 - a^4 - 5*a^3 + 3*a^2 + 8*a - 11;
	Us := [u2^e2 * u3^e3 * u4^e4 : e2,e3,e4 in [-1..1]];
	// Scale by units
	h := Max([myheight(c) : c in coords_new]);
	repeat
		changed := false;
		coords_new_tmp := coords_new;
		for u in Us do
			coords_new_new := [c / u : c in coords_new];
			if  h gt Max([myheight(c) : c in coords_new_new]) then
				h := Max([myheight(c) : c in coords_new_new]);
				coords_new_tmp := coords_new_new;
				changed := true;
			end if;
		end for;
		coords_new := coords_new_tmp;
	until not changed;

	return coords_new;
end intrinsic;