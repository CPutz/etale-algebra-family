// Load this file from the main folder
AttachSpec("spec");

Q := Rationals();

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
printf "We perform the computations from Proposition 4.23.\n";
printf "==================================================================\n\n";

load "scripts/257/covering_sets.dat";

// LMFDB data
load "scripts/257/fields_cubic_unramified257.dat";
L3 := make_data();
printf "\nThere exist %o cubic number fields with signature (1,1) and unramfied outside 2, 5 and 7\n\n", #L3;

// LMFDB data
load "scripts/257/fields_quintic_unramified257.dat";
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
quit;