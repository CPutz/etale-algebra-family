// Load this file from the main folder
AttachSpec("spec");

// Returns whether U is a valid local covering set of isomorphism
// classes of etale algebras for L
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

load "scripts/357/local_covering_sets.dat";

printf "Performing calculations for p=2\n";
E2 := EtaleAlgebras357(2);
assert valid_covering_set(E2,U2);
assert valid_covering_set(U2,E2);
printf "valid local covering set for p=2\n\n";

printf "Performing calculations for p=3\n";
E3 := EtaleAlgebras357(3);
assert valid_covering_set(E3,U3);
assert valid_covering_set(U3,E3);
printf "valid local covering set for p=3\n\n";

printf "Performing calculations for p=5\n";
E5 := EtaleAlgebras357(5);
assert valid_covering_set(E5,U5);
assert valid_covering_set(U5,E5);
printf "valid local covering set for p=5\n\n";

printf "Performing calculations for p=7\n";
E7 := EtaleAlgebras357(7);
assert valid_covering_set(E7,U7);
assert valid_covering_set(U7,E7);
printf "valid local covering set for p=7\n\n";

printf "done\n";
quit;