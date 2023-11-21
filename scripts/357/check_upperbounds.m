// Load this file from the main folder
AttachSpec("spec");

// Returns whether U is a valid upper bound of isomorphism
// classes of etale algebras for L
function valid_upper_bound(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

load "scripts/357/upperbounds.m";

printf "Performing calculations for p=2\n";
E2 := EtaleAlgebras357(2);
assert valid_upper_bound(E2,U2);
assert valid_upper_bound(U2,E2);
printf "valid upper bound for p=2\n\n";

printf "Performing calculations for p=3\n";
E3 := EtaleAlgebras357(3);
assert valid_upper_bound(E3,U3);
assert valid_upper_bound(U3,E3);
printf "valid upper bound for p=3\n\n";

printf "Performing calculations for p=5\n";
E5 := EtaleAlgebras357(5);
assert valid_upper_bound(E5,U5);
assert valid_upper_bound(U5,E5);
printf "valid upper bound for p=5\n\n";

printf "Performing calculations for p=7\n";
E7 := EtaleAlgebras357(7);
assert valid_upper_bound(E7,U7);
assert valid_upper_bound(U7,E7);
printf "valid upper bound for p=7\n\n";
