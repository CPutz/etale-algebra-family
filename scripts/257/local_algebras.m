// Load this file from the main folder
AttachSpec("spec");

// Returns whether U is a valid covering set of isomorphism
// classes of etale algebras for L
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

load "scripts/257/covering_sets.m";

printf "\n==================================================================\n";
printf "We perform the computations for Theorem 5.6. We verify that the\n";
printf "local covering sets as defined in the file covering_sets.m\n";
printf "(which correspond to the sets given in Theorem 5.6) are correct\n";
printf "and are minimal.\n";
printf "==================================================================\n\n";

SetVerbose("AlgEtFam",1);

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
time E2 := EtaleAlgebras257(2 : Simplify := false);

assert valid_covering_set(U2, E2); //sufficient
assert valid_covering_set(E2, U2); //necessary
printf "valid and minimal covering set the prime 2\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";
time E3 := EtaleAlgebras257(3 : Simplify := false);

assert valid_covering_set(U3, E3); //sufficient
assert valid_covering_set(E3, U3); //necessary
printf "valid and minimal covering set the prime 3\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 5\n";
printf "------------------------------------------------------------------\n\n";
time E5 := EtaleAlgebras257(5 : Simplify := false);

assert valid_covering_set(U5, E5); //sufficient
assert valid_covering_set(E5, U5); //necessary
printf "valid and minimal covering set the prime 5\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 7\n";
printf "------------------------------------------------------------------\n\n";
time E7 := EtaleAlgebras257(7 : Simplify := false);

assert valid_covering_set(U7, E7); //sufficient
assert valid_covering_set(E7, U7); //necessary
printf "valid and minimal covering set the prime 7\n\n";

printf "done\n";