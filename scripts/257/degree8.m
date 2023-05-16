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

function quadratic_extensions_etale_algebras_field(L,B);
	exts := [];
	for K in AllExtensions(L,2) do
		E := EtaleAlgebra([FieldOfFractions(AbsoluteTotallyRamifiedExtension(K))], B);
		E`BaseRing := B;
		Append(~exts, E);
	end for;
	return exts cat [EtaleAlgebra([L,L], B)];
end function;

function quadratic_extensions_etale_algebras(E);
	B := BaseRing(E);
	Cs := [quadratic_extensions_etale_algebras_field(K,B) : K in Components(E)];
	C := CartesianProduct(Cs);
	return [DirectProduct([c : c in cs]) : cs in C];
end function;

// Computes all quadratic extensions of a number field K,
// only ramified above the primes in P
function quadratic_extensions(K,P);
	G,phi := pSelmerGroup(2,P);
	values := [g@@phi : g in G];
	R<x> := PolynomialRing(K);
	return [AbsoluteField(ext<K | x^2 - v>) : v in values | IsIrreducible(x^2 - v)];
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/upperbounds.m";

// LMFDB data
load "misc/scripts/257/fields_quartic_unramified257.m";
L4 := make_data();
printf "\nThere exist %o quartic number fields unramfied outside 2, 5 and 7\n\n", #L4;

time L4_filter := [ L : L in L4 |
	exists {E : E in quadratic_extensions_etale_algebras(EtaleAlgebra(L,3)) |
		exists { E3 : E3 in U3 | IsIsomorphic(E,E3) } } and
	exists {E : E in quadratic_extensions_etale_algebras(EtaleAlgebra(L,5)) |
		exists { E5 : E5 in U5 | IsIsomorphic(E,E5) } } and
	exists {E : E in quadratic_extensions_etale_algebras(EtaleAlgebra(L,7)) |
		exists { E7 : E7 in U7 | IsIsomorphic(E,E7) } } and
	exists {E : E in quadratic_extensions_etale_algebras(EtaleAlgebra(L,2)) |
		exists { E2 : E2 in U2 | IsIsomorphic(E,E2) } } ];

assert #L4_filter eq 1;
L := L4_filter[1];
printf "There exists 1 quartic number field satisfying all local conditions at 2, 3, 5 and 7: %o\n", L;

OL := Integers(L);
L8 := [K : K in quadratic_extensions(L,Support(2*5*7*OL)) |
	exists { E : E in U3 | IsIsomorphic(E, EtaleAlgebra(K,3)) } and
	exists { E : E in U5 | IsIsomorphic(E, EtaleAlgebra(K,5)) } and
	exists { E : E in U7 | IsIsomorphic(E, EtaleAlgebra(K,7)) } and
	exists { E : E in U2 | IsIsomorphic(E, EtaleAlgebra(K,2)) }];

printf "There exists %o octic number fields satisfying all local conditions at 2, 3, 5 and 7,", #L8;
printf "and having L as a quartic subfield: %o\n", L8;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/covering.m";

printf "Computing a full-rank subgroup of the Mordell-Weil group of E over %o\n", L;

EL := BaseChange(E,L);
_,G,GtoEL := PseudoMordellWeilGroup(EL);

rankbound := RankBound(EL);
//rankbound := 2;
assert rankbound eq TorsionFreeRank(G);

print "Found full-rank subgroup of E(L) (rank = %o)\n", TorsionFreeRank(G);

gens := [GtoEL(g) : g in Generators(G)];
sat23 := Saturation(Saturation([EL!p : p in gens], 2), 3);
A := AbelianGroup([Order(g) : g in sat23]);
AtoEL := map< A -> EL | x :-> &+[Eltseq(x)[i]*sat23[i] : i in [1..#sat23]] >;

printf "Constructed subgroup which is saturated at 2 and 3.\n";

printf "Performing elliptic curve Chabauty\n";

PhiEL := map< EL -> P1 | DefiningEquations(PhiE) >;

time V,R := Chabauty(AtoEL, PhiEL : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};


pts_EL := { AtoEL(v) : v in V };
printf "The points in E(L) with rational image under Φ_E are %o\n", pts_EL;

CL := BaseChange(C,L);
CLtoEL := map< CL -> EL | DefiningEquations(CtoCsigma * CsigmatoE0 * E0toE) >;

pts_CL := {@ @};
for p in pts_EL do
	S := Cluster(EL, p);
	pts_CL join:= RationalPoints(Pullback(CLtoEL, S));
end for;

printf "The points in C(L) with rational image under ϕ are %o\n", pts_CL;

printf "\ndone\n";