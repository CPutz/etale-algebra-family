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
// only ramified above the primes in S
function quadratic_extensions(K,S);
	//A/A^2 where A is the ring of S-units of K
	G,phi := pSelmerGroup(2,S);
	values := [g@@phi : g in G];
	R<x> := PolynomialRing(K);
	return [AbsoluteField(ext<K | x^2 - v>) : v in values | IsIrreducible(x^2 - v)];
end function;

// Computes all degree n field extensions of L where
// L is a p-adic field with base ring B
function local_field_extensions(L,n,B);
	exts := [];
	for K in AllExtensions(L,n) do
		E := EtaleAlgebra([FieldOfFractions(AbsoluteTotallyRamifiedExtension(K))], B);
		E`BaseRing := B;
		Append(~exts, E);
	end for;
	return exts;
end function;

// Computes all degree n etale algebra extensions of L where
// L is a p-adic field with base ring B
function local_etale_extensions_of_field(L,n,B);
	exts_degree := [];
	for d := 1 to n do
		Append(~exts_degree, local_field_extensions(L,d,B));
	end for;

	exts := [];
	for P in Partitions(n) do
		C := [DirectProduct([e : e in c]) : c in CartesianProduct([exts_degree[p] : p in P])];
		exts cat:= C;
	end for;

	return exts;
end function;

// Computes all degree n etale algebra extensions of E where
// E is a p-adic etale algebra
function local_etale_extensions(E,n);
	B := BaseRing(E);
	Cs := [local_etale_extensions_of_field(K,n,B) : K in Components(E)];
	C := CartesianProduct(Cs);
	return [DirectProduct([c : c in cs]) : cs in C];
end function;

// generates all subpartitions of p
function subpartitions(p);
	C := CartesianProduct([Partitions(r) : r in p]);
	return SetToSequence({@ {* r : r in ci, ci in c *} : c in C @});
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 5.11.\n";
printf "==================================================================\n\n";

load "scripts/257/covering_sets.m";

E2 := [ E : E in U2 |
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,1,1]) or
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 2: %o\n",
	{ Valuation(Discriminant(E)) : E in E2 };

E5 := [ E : E in U5 |
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,1,1]) or
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 5: %o\n",
	{ Valuation(Discriminant(E)) : E in E5 };

E7 := [ E : E in U7 |
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,1,1]) or
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,2]) ];

printf "Valuation of possible local discriminants at 7: %o\n",
	{ Valuation(Discriminant(E)) : E in E7 };


printf "\nRuling out cubic subfields.\n";
load "scripts/257/fields_cubic_unramified57.dat";
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
//L2 contains all quadratic number fields only ramified at 5 and 7
L2 := [NumberField(f) : e,a,b in [0,1] |
	IsIrreducible(f) and
	PrimeDivisors(Discriminant(Integers(NumberField(f)))) subset [5,7]
	where f := x^2 - (-1)^e * 5^a * 7^b];
printf "Possible candidates for quadratic subfield: %o\n", L2;

// Either 5 is inert in K, or 7 is inert in K, or 3 splits in K
assert forall { K : K in L2 |
	IsInert(Ideal(Decomposition(K,5)[1,1])) or
	IsInert(Ideal(Decomposition(K,7)[1,1])) or
	IsSplit(Ideal(Decomposition(K,3)[1,1]))	};

// Alternatively, one can compute all local cubic extensions of the
// quadratic fields in L2 and see that non satisfy both the local conditions at 5 and 7
assert forall { L : L in L2 |
	not exists {E : E in U5 | exists { E2 : E2 in local_etale_extensions(EtaleAlgebra(L,5),3) |
			contains_components_isomorphic_to(E,E2) } } or
	not exists {E : E in U7 | exists { E2 : E2 in local_etale_extensions(EtaleAlgebra(L,7),3) |
			contains_components_isomorphic_to(E,E2) } } };

printf "Quadratic subfields have been ruled out.\n";

printf "\nComputations for the primitive case.\n";

E5_611 := [ SimplifyToProduct(E) : E in U5 |
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,1,1]) ];

E7_611 := [ SimplifyToProduct(E) : E in U7 |
	SequenceToMultiset(FactorizationPattern(E)) in subpartitions([6,1,1]) ];

printf "\nCase where K is isomorphic to M x Q x Q:\n";
printf "K tensor Q_5 is isomorphic to: %o\n", E5_611;
printf "K tensor Q_7 is isomorphic to: %o\n", E7_611;

printf "\nCase where K is isomorphic to M x L with L a quadratic number field:\n";
printf "Possible candidates for L: %o\n", L2;

for L in L2 do
	printf "\nSuppose L is isomorphic to %o.\n", L;
	E5_L := [ SimplifyToProduct(E) : E in U5 | contains_components_isomorphic_to(E, EtaleAlgebra(L,5)) ];
	E7_L := [ SimplifyToProduct(E) : E in U7 | contains_components_isomorphic_to(E, EtaleAlgebra(L,7)) ];
	if #E5_L eq 0 then
		printf "Then we get an obstruction at the prime 5.\n";
	elif #E7_L eq 0 then
		printf "Then we get an obstruction at the prime 7.\n";
	else
		printf "Then K tensor Q_5 must be isomorphic to one of %o etale algebras: %o,\n", #E5_L, E5_L;
		printf "and K tensor Q_7 must be isomorphic to one of %o etale algebras: %o.\n", #E7_L, E7_L;
	end if;
end for;

print "\ndone\n";
quit;