// Load this file from the main folder
AttachSpec("spec");

// Returns whether L is contained in U up to isomorphsim
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

printf "\n==================================================================\n";
printf "We perform the computations for Proposition 6.18. \n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
Q2 := pAdicField(2,500);
U2 := [EtaleAlgebra([UnramifiedExtension(Q2,n) : n in e], Q2) : e in [[10,1], [5,3,2,1], [4,4,2,1]]];

E2 := EtaleAlgebras3511Coeff(2, 1, 1, 1);

assert valid_covering_set(U2, E2); //sufficient
assert valid_covering_set(E2, U2); //necessary
printf "valid and minimal covering set the prime 2\n\n";

printf "\n==================================================================\n";
printf "We perform the computations for Proposition 6.12. \n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";

Q3 := pAdicField(3,500);

printf "case v3(a) = 4\n";
U3_a34 := 