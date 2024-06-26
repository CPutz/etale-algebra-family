// Load this file from the main folder
AttachSpec("spec");
load "scripts/257/covering_sets.dat";

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

// Computes all degree n field extensions of L where
// L is a p-adic field with base ring B
function local_field_extensions(L,n,B);
	exts := [];
	//hack
	if Degree(L) eq 1 then
		L := BaseRing(L);
	end if;
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
printf "We perform the computations from Proposition 4.28.\n";
printf "==================================================================\n\n";

// Shows that 5 must split in M
Q5 := pAdicField(5,500);
E5_2 := local_etale_extensions_of_field(Q5, 2, Q5);
E5_2_filter := [ E : E in E5_2 |
	exists {<E8,E2> : E8 in local_etale_extensions(E,4),
					  E2 in U5 |
					  	IsIsomorphic(E8,E2)} ];

// Shows that M \otimes Q_7 = Q_7(sqrt(7))
Q7 := pAdicField(7,500);
E7_2 := local_etale_extensions_of_field(Q7, 2, Q7);
E7_2_filter := [ E : E in E7_2 |
	exists {<E8,E2> : E8 in local_etale_extensions(E,4),
					  E2 in U7 |
					  	IsIsomorphic(E8,E2)} ];

//	quadratic extensions unramified outside 2, 5 and 7
quad := [QuadraticField((-1)^a * 2^b * 5^c * 7^d) : a,b,c,d in [0,1] | <a,b,c,d> ne <0,0,0,0>];
quad_filter := [ K : K in quad |
	exists { E5 : E5 in E5_2_filter | IsIsomorphic(E5, EtaleAlgebra(K,5)) } and
	exists { E7 : E7 in E7_2_filter | IsIsomorphic(E7, EtaleAlgebra(K,7)) }	];

assert #quad_filter eq 1;

M := quad_filter[1];
printf "There exists 1 quadratic number field satisfying all local conditions at 5 and 7: %o\n", M;

_<t> := PolynomialRing(Rationals());
assert forall { E2 : E2 in U2 |
	forall { C : C in Components(E2) | not HasRoot(t^2 - 14, C) } };

printf "None of the local algebras at 2 is an extension of Q(sqrt(14)).\n";

printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.29.\n";
printf "==================================================================\n\n";

// LMFDB data
load "scripts/257/fields_quartic_unramified257.dat";
L4 := make_data();
printf "\nThere exist %o quartic number fields unramfied outside 2, 5 and 7\n\n", #L4;

L4_filter := [ L : L in L4 |
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

printf "\n==================================================================\n";
printf "We perform the computations from Remark 4.30.\n";
printf "==================================================================\n\n";

OL := Integers(L);
L8 := [K : K in quadratic_extensions(L,Support(2*5*7*OL)) |
	exists { E : E in U3 | IsIsomorphic(E, EtaleAlgebra(K,3)) } and
	exists { E : E in U5 | IsIsomorphic(E, EtaleAlgebra(K,5)) } and
	exists { E : E in U7 | IsIsomorphic(E, EtaleAlgebra(K,7)) } and
	exists { E : E in U2 | IsIsomorphic(E, EtaleAlgebra(K,2)) }];

printf "There exists %o octic number fields satisfying all local conditions at 2, 3, 5 and 7,", #L8;
printf "and having L as a quartic subfield: %o\n", L8;

printf "\ndone\n";
quit;