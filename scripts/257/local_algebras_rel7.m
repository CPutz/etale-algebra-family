// Load this file from the main folder
AttachSpec("spec");

// Returns whether L is contained in U up to isomorphsim
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

K := QuadraticField(21);

load "scripts/257/covering_sets_rel7.dat";

printf "\n==================================================================\n";
printf "We perform the computations for Theorem 5.39. We verify that the\n";
printf "local covering sets as defined in the file covering_sets_rel7.m\n";
printf "(which correspond to the sets given in Theorem 5.39) are correct\n";
printf "and are minimal.\n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime above 2\n";
printf "------------------------------------------------------------------\n\n";
p2 := Decomposition(K,2)[1,1];
E2 := EtaleAlgebras257Relative(p2);

assert valid_covering_set(U2, E2); //sufficient
assert valid_covering_set(E2, U2); //necessary
printf "correct and minimal covering set at the prime above 2\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime above 3\n";
printf "------------------------------------------------------------------\n\n";
p3 := Decomposition(K,3)[1,1];
E3 := EtaleAlgebras257Relative(p3);

assert valid_covering_set(U3, E3); //sufficient
assert valid_covering_set(E3, U3); //necessary
printf "valid and minimal covering set at the prime above 3\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the primes above 5\n";
printf "------------------------------------------------------------------\n\n";
p51 := Decomposition(K,5)[1,1];
E51 := EtaleAlgebras257Relative(p51);

assert valid_covering_set(U51, E51); //sufficient
assert valid_covering_set(E51, U51); //necessary
printf "valid and minimal covering set at the first prime above 5\n\n";

p52 := Decomposition(K,5)[2,1];
E52 := EtaleAlgebras257Relative(p52);

assert valid_covering_set(U52, E52); //sufficient
assert valid_covering_set(E52, U52); //necessary
printf "valid and minimal covering set at the second prime above 5\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime above 7\n";
printf "------------------------------------------------------------------\n\n";
p7 := Decomposition(K,7)[1,1];
E7 := EtaleAlgebras257Relative(p7);

assert valid_covering_set(U7, E7); //sufficient
assert valid_covering_set(E7, U7); //necessary
printf "valid and minimal covering set the prime 7\n\n";

printf "done\n";
quit;