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

// Computes all quadratic extensions of a number field K,
// only ramified above the primes in P
function quadratic_extensions(K,P);
	G,phi := pSelmerGroup(2,P);
	values := [g@@phi : g in G];
	R<x> := PolynomialRing(K);
	return [AbsoluteField(ext<K | x^2 - v>) : v in values | IsIrreducible(x^2 - v)];
end function;


function splitting_partition(E);
	return {* Degree(C[1],BaseRing(E)) ^^ C[2] : C in ComponentsIsoStructure(E) *};
end function;

// generates all subpartitions of p
function subpartitions(p);
	C := CartesianProduct([Partitions(r) : r in p]);
	return SetToSequence({@ {* r : r in ci, ci in c *} : c in C @});
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/upperbounds.m";

E2 := [ E : E in U2 |
	splitting_partition(E) in subpartitions([6,1,1]) or
	splitting_partition(E) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 2: %o\n",
	{ Valuation(Discriminant(E)) : E in E2 };

E5 := [ E : E in U5 |
	splitting_partition(E) in subpartitions([6,1,1]) or
	splitting_partition(E) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 5: %o\n",
	{ Valuation(Discriminant(E)) : E in E5 };

E7 := [ E : E in U7 |
	splitting_partition(E) in subpartitions([6,1,1]) or
	splitting_partition(E) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 7: %o\n",
	{ Valuation(Discriminant(E)) : E in E7 };


printf "\nRuling out cubic subfields.\n";
load "misc/scripts/257/fields_cubic_unramified57.m";
L3 := make_data();
printf "Possible candidates for cubic subfield: %o\n", L3;

// Rule out both candidates by computing their quadratic extensions
// and comparing with the local etale algebras for the primes 5 and 7 
for K in L3 do
	printf "Computing quadratic extensions and checking local conditions.\n";
	OK := Integers(K);
	// The primes above 5 and 7
	Ps := Support(35*OK);
	// The quadratic extensions of K unramified outside 5 and 7
	Ms := [M : M in quadratic_extensions(K, Ps)];
	// Find the M's which satsify the local conditions at 5 and 7
	Ms_filter := [ M : M in Ms |
		exists {E : E in U5 | contains_components_isomorphic_to(E, EtaleAlgebra(M,5)) } and
		exists {E : E in U7 | contains_components_isomorphic_to(E, EtaleAlgebra(M,7)) } ];
	// No extension satsifies all local conditions
	assert #Ms_filter eq 0;
end for;

printf "Cubic subfields have been ruled out.\n";

printf "\nRuling out quadratic subfields.\n";
L2 := [NumberField(f) : e in [1,-1], a in [0,1], b in [0,1] |
	IsIrreducible(f) and
	PrimeDivisors(Discriminant(Integers(NumberField(f)))) subset [5,7]
	where f := x^2 - e * 5^a * 7^b];
printf "Possible candidates for cubic subfield: %o\n", L2;

// Either 5 is inert in K, or 7 is inert in K, or 3 splits in K
assert forall { K : K in L2 |
	IsInert(Ideal(Decomposition(K,5)[1,1])) or
	IsInert(Ideal(Decomposition(K,7)[1,1])) or
	IsSplit(Ideal(Decomposition(K,3)[1,1]))	};

printf "Quadratic subfields have been ruled out.\n";