//Constants
Z := Integers();
Q := Integers();


intrinsic abcTriplesFromjInvariant(j::FldRatElt) -> SeqEnum[Tup]
{Produces abc triples from an elliptic curve with j-invariant j}
	Qx<x> := PolynomialRing(Rationals());
	f := 256 * (x^2 + x + 1)^3 - j * x^2 * (x + 1)^2;
	roots := [r[1] : r in Roots(f)];
	return [<Denominator(r), Numerator(r), Denominator(r) + Numerator(r)> : r in roots];
end intrinsic;

intrinsic abcTriplesFromCremonaDatabaseSmallPrimes() -> SeqEnum[Tup]
{Produces a sequence of abcTriples using the Cremona elliptic curve database
but only for elliptic curves with primes 2, 3, 5, 7 and 11 in the conductor}
	D := EllipticCurveDatabase();
	Ns := [2^a * 3^b3 * 5^b5 * 7^b7 * 11^b11 : a in [0..8], b3, b5, b7, b11, b13 in [0,1]];
	Es := [E : E in EllipticCurves(D, N), N in Ns];
	return {@ c : c in abcTriplesFromjInvariant(jInvariant(E)), E in Es @};
end intrinsic;

intrinsic abcTriplesFromCremonaDatabase() -> SeqEnum[Tup]
{Produces a sequence of abcTriples using the entire Cremona elliptic curve database}
	D := EllipticCurveDatabase();
	return {@ c : c in abcTriplesFromjInvariant(jInvariant(E)), E in EllipticCurves(D) @};
end intrinsic;

intrinsic abcTriplesFromDatabaseLarge() -> SeqEnum[Tup]
{Produces a sequence of abcTriples using the Cremona elliptic curve database}
	D := EllipticCurveDatabaseLarge();
	return {@ c : c in abcTriplesFromjInvariant(jInvariant(E)), E in EllipticCurves(D) @};
end intrinsic;

intrinsic abcTriplesFromMatschke() -> SeqEnum[Tup]
{Produces a sequence of abcTriples using the Cremona elliptic curve database}
	I := Read("Dropbox/PhD/Magma/EtaleAlgebras/curves.txt");
	S := StringToIntegerSequence(I);
	pairs := [<S[2*i+1], S[2*i+2]> : i in [0..#S/2-1]];
	return {@ c : c in abcTriplesFromjInvariant(Q!1728 * p[1]^3 / (p[1]^3 - p[2]^2)), p in pairs @};
end intrinsic;

intrinsic IsPseudoSolution(t::Tup, p::RngIntElt, q::RngIntElt, r::RngIntElt) -> BoolElt
{Determines whether the abc triple t is a pseudo solution of the generalized
Fermat equation with exponents (p,q,r)}
	require IsPrime(p) and IsPrime(q) and IsPrime(r): "Arguments 2, 3 and 4 need to be prime";
	a := Z!(t[1] / (p^Valuation(t[1], p) * q^Valuation(t[1], q) * r^Valuation(t[1], r)));
	b := Z!(t[2] / (p^Valuation(t[2], p) * q^Valuation(t[2], q) * r^Valuation(t[2], r)));
	c := Z!(t[3] / (p^Valuation(t[3], p) * q^Valuation(t[3], q) * r^Valuation(t[3], r)));
	return IsPower(a, p) and IsPower(b, q) and IsPower(c, r);
end intrinsic;

//for the time being
Algebras357_7 := function()
	R<t> := PolynomialRing(pAdicField(7,500));
	Ps := [t*(t^6+7), t*(t^6+14), t*(t^6+28),
		   t^7+7*t+7, t^7+14*t+7, t^7+28*t+7,
		   (t^2-7)*(t^5-7),
		   (t^4-7)*(t^3-7), (t^4-7)*(t^3-14), (t^4-7)*(t^3-28)];
	return [EtaleAlgebra(P) : P in Ps];
end function;

Algebras357_5 := function()
	R<t> := PolynomialRing(pAdicField(5,500));
	Ps := [t*(t^2-10)*(t^4-5), t*(t^2-10)*(t^4+5),
		   (t^2-10)*(t^5+5*t+5), (t^2-10)*(t^5+20*t+5),
		   (t^2-10)^2*(t^3-5), t^7-5];
	return [EtaleAlgebra(P) : P in Ps];
end function;

Algebras357_3 := function()
	R<t> := PolynomialRing(pAdicField(3,500));
	Ps := [t*(t^6+6*t^3+9*t^2+9), 7*(15*t^7 - 35*t^6 + 21*t^5) + 25,
		   t^2*(t^5-3),
		   t*(t^6+3*t^2+6*t+3), t*(t^6-3*t^2-6*t-3),
		   t^2*(t^2-3)*(t^3+3*t+3),
		   t^3*(t^2-3)*(t^2+3),
		   t^7-3];
	return [EtaleAlgebra(P) : P in Ps];
end function;

intrinsic FilterPseudoSolutions357(L::SeqEnum[Tup]) -> SeqEnum[Tup]
{Removes all pseudo solutions which can be detected by a local obstruction}
	L3 := Algebras357_3();
	L5 := Algebras357_5();
	L7 := Algebras357_7();

	R<t> := PolynomialRing(Integers());
	R3 := PolynomialRing(pAdicField(3,500));
	R5 := PolynomialRing(pAdicField(5,500));
	R7 := PolynomialRing(pAdicField(7,500));
	phi := 15*t^7 - 35*t^6 + 21*t^5;

	res := [];
	for t in L do
		E3 := EtaleAlgebra(R3!(t[3] * phi - t[1]));
		if exists(c3) {E : E in L3 | IsIsomorphic(E, E3)} then
			E5 := EtaleAlgebra(R5!(t[3] * phi - t[1]));
			if exists(c5) {E : E in L5 | IsIsomorphic(E, E5)} then
				E7 := EtaleAlgebra(R7!(t[3] * phi - t[1]));
				if exists(c7) {E : E in L7 | IsIsomorphic(E, E7)} then
					Append(~res, t);
				end if;
			end if;
		end if;
	end for;
	return res;
end intrinsic;


EtaleAlgebras257 := function(p)
	D := LocalFieldDatabase();
	Z := Integers();
	R<t> := PolynomialRing(pAdicField(p,500));
	phi1 := 4*t^5*(14+14*t+20*t^2+25*t^3);
	phi2 := 4*t - 1;
	B0 := [Z!b : b in Integers(p^4) | Integers(p) ! b notin [0,1]];
	B  := [Z!b : b in Integers(p^3) | Integers(p) ! b ne 0];

	Ls0 := EtaleAlgebraListIsomorphism([phi1 - phi2*b : b in B0]: D := D);
	Ls1 := EtaleAlgebraListIsomorphism([phi1 - phi2*b*p^(5*r)       : b in B, r in [1..4]]: D := D);
	Ls2 := EtaleAlgebraListIsomorphism([phi1 - phi2*(1 + b*p^(2*r)) : b in B, r in [1..4]]: D := D);
	Ls3 := EtaleAlgebraListIsomorphism([p^(7*r)*phi1 - phi2*b       : b in B, r in [1..4]]: D := D);

	return [Ls0, Ls1, Ls2, Ls3];
end function;

intrinsic FilterPseudoSolutions257(L::SeqEnum[Tup],
	L2::SeqEnum[EtAlg], L5::SeqEnum[EtAlg],L7::SeqEnum[EtAlg]) -> SeqEnum[Tup]
{Removes all pseudo solutions which can be detected by a local obstruction}
	//printf "Computing isomorphism classes for 257\n";
	//L2 := IsomorphismClassesEtale(&cat EtaleAlgebras257(2));
	//L5 := IsomorphismClassesEtale(&cat EtaleAlgebras257(5));
	//L7 := IsomorphismClassesEtale(&cat EtaleAlgebras257(7));

	R<t> := PolynomialRing(Integers());
	R2 := PolynomialRing(pAdicRing(2,500));
	R5 := PolynomialRing(pAdicRing(5,500));
	R7 := PolynomialRing(pAdicRing(7,500));
	S2 := PolynomialRing(pAdicField(2,500));
	S5 := PolynomialRing(pAdicField(5,500));
	S7 := PolynomialRing(pAdicField(7,500));
	phi1 := 4*t^5*(14+14*t+20*t^2+25*t^3);
	phi2 := 4*t - 1;

	res := [];
	for t in L do
		f := t[3] * phi1 - t[1] * phi2;
		f2 := Factorization(R2 ! MakeMonicIntegral(S2 ! f));
		if exists(c2) {E : E in L2 | IsDefiningPolynomialEtale(E, f2)} then
			f5 := Factorization(R5 ! MakeMonicIntegral(S5 ! f));
			if exists(c5) {E : E in L5 | IsDefiningPolynomialEtale(E, f5)} then
				f7 := Factorization(R7 ! MakeMonicIntegral(S7 ! f));
				if exists(c7) {E : E in L7 | IsDefiningPolynomialEtale(E, f7)} then
					Append(~res, t);
				end if;
			end if;
		end if;
		printf ".";
	end for;
	printf "\n";
	return res;
end intrinsic;
