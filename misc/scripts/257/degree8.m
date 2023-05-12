// Load this file from the main folder
AttachSpec("spec");

function contains_components_isomorphic_to(E1,E2);
	C1 := Components(E1);
	C2 := Components(E2);

	I := [];
	// For every component of E2, find an isomorphic component of E1,
	// and make sure that no components are ``used twice''
	for C in C2 do
		b := exists (i) { i : i in [1..#C1] | i notin I and IsIsomorphic(C,C1[i]) };
		if not b then
			return false;
		end if;
		Append(~I, i);
	end for;

	return true;
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/covering.m";

_<x> := PolynomialRing(Rationals());
L := NumberField(x^4 - 2*x^3 - 2*x^2 - 4*x - 10);

printf "Computing a full-rank subgroup of the Mordell-Weil group of E1 over %o\n", L;

E1L := BaseChange(E1,L);
_,G,GtoE1L := PseudoMordellWeilGroup(E1L);

rankbound := RankBound(E1L);
//rankbound := 2;
assert rankbound eq TorsionFreeRank(G);

print "Found full-rank subgroup of E1(L) (rank = %o)\n", TorsionFreeRank(G);

gens := [GtoE1L(g) : g in Generators(G)];
sat23 := Saturation(Saturation([E1L!p : p in gens], 2), 3);
A := AbelianGroup([Order(g) : g in sat23]);
AtoE1L := map< A -> E1L | x :-> &+[Eltseq(x)[i]*sat23[i] : i in [1..#sat23]] >;

printf "Constructed subgroup which is saturated at 2 and 3.\n";

printf "Performing elliptic curve Chabauty\n";

PhiE1L := map< E1L -> P1 | DefiningEquations(PhiE1) >;

time V,R := Chabauty(AtoE1L, PhiE1L : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};


pts_E1L := { AtoE1L(v) : v in V };
printf "The points in E1(L) with rational image under Φ_E1 are %o\n", pts_E1L;

CL := BaseChange(C,L);
CLtoE1L := map< CL -> E1L | DefiningEquations(CtoCsigma * CsigmatoE0 * E0toE1) >;

pts_CL := {@ @};
for p in pts_E1L do
	S := Cluster(E1L, p);
	pts_CL join:= RationalPoints(Pullback(CLtoE1L, S));
end for;

printf "The points in C(L) with rational image under ϕ are %o\n", pts_CL;

printf "\ndone\n";