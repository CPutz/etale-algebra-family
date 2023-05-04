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

load "misc/scripts/257/upperbounds.m";

// LMFDB data
load "misc/scripts/257/fields_cubic_unramified257.m";
L3 := make_data();
printf "\nThere exist %o cubic number fields with signature (1,1) and unramfied outside 2, 5 and 7\n\n", #L3;

// LMFDB data
load "misc/scripts/257/fields_quintic_unramified257.m";
L5 := make_data();
printf "\nThere exist %o quintic number fields with signature (1,2) and unramfied outside 2, 5 and 7\n\n", #L5;


// Filter L3 for number fields that agree with the local data at 2, 5 and 7
L3_filter := [ L : L in L3 |
	exists {E : E in U2 | contains_components_isomorphic_to(E, EtaleAlgebra(L,2)) } and
	exists {E : E in U5 | contains_components_isomorphic_to(E, EtaleAlgebra(L,5)) } and
	exists {E : E in U7 | contains_components_isomorphic_to(E, EtaleAlgebra(L,7)) } ];

printf "The following cubic number fields remain after checking local conditions at 2, 5 and 7: %o\n\n", L3_filter;

// Filter L5 for number fields that agree with the local data at 2, 5 and 7
L5_filter := [ L : L in L5 |
	exists {E : E in U2 | contains_components_isomorphic_to(E, EtaleAlgebra(L,2)) } and
	exists {E : E in U5 | contains_components_isomorphic_to(E, EtaleAlgebra(L,5)) } and
	exists {E : E in U7 | contains_components_isomorphic_to(E, EtaleAlgebra(L,7)) } ];

printf "The following quintic number fields remain after checking local conditions at 2, 5 and 7: %o\n\n", L5_filter;

L := [ <K5, K3> : K5 in L5_filter, K3 in L3_filter ];
L_filter := [K : K in L |
	exists {E : E in U2 | IsIsomorphic(E, DirectProduct([EtaleAlgebra(K[1],2), EtaleAlgebra(K[2],2)])) } and 
	exists {E : E in U5 | IsIsomorphic(E, DirectProduct([EtaleAlgebra(K[1],5), EtaleAlgebra(K[2],5)])) } and 
	exists {E : E in U7 | IsIsomorphic(E, DirectProduct([EtaleAlgebra(K[1],7), EtaleAlgebra(K[2],7)])) } ];

printf "The following etale algebras remain after checking local conditions at 2, 5 and 7: %o\n\n", L_filter;

printf "\ndone\n";


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/covering.m";

_<x> := PolynomialRing(Rationals());
M := NumberField(25*x^3 + 20*x^2 + 14*x + 14);
assert #L3_filter eq 1;
assert IsIsomorphic(L3_filter[1], M);
L := SplittingField(L3_filter[1]);

printf "Computing a full-rank subgroup of the Mordell-Weil group of E1 over %o\n", L;

E1L := BaseChange(E1,L);
_,G,GtoE1L := PseudoMordellWeilGroup(E1L);

//rankbound := RankBound(E1L);
rankbound := 2;
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

F := x * (25*x^3 + 20*x^2 + 14*x + 14);
assert forall { p : p in pts_CL | p[3] eq 0 or (Evaluate(F,p[1]) eq 0 and Evaluate(F,p[2]) eq 0 and p[3] eq 1) };

printf "\nThe coordinates all these points are roots of X * (25X^3 + 20X^2 + 14X + 14).\n";

assert forall { p : p in pts_CL | p[3] eq 0 or Phi(C(L)!Eltseq(p)) eq P1![0,1] };

printf "All points (except for the points at infinity) map to (0 : 1) under ϕ.\n";


printf "\ndone\n";