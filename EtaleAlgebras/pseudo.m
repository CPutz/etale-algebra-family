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