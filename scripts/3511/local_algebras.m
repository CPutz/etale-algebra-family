// Load this file from the main folder
AttachSpec("spec");

printf "--- Warning ---\n";
printf "Page and theorem numbers mentioned below are currently not correct.\n";
printf "---------------\n\n";

// Returns whether L is contained in U up to isomorphsim
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

load "scripts/3511/local_covering_sets.dat";

printf "\n==================================================================\n";
printf "We perform the computations for Proposition 5.20. \n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
E2 := EtaleAlgebras3511Coeff(2, 1, 1, 1);

assert valid_covering_set(U2, E2); //sufficient
assert valid_covering_set(E2, U2); //necessary
printf "valid and minimal covering set at the prime 2\n\n";


printf "\n==================================================================\n";
printf "We perform the computations for Proposition 5.14. \n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";

printf "case v3(a) = 4\n";
E3_va4 := EtaleAlgebras3511Coeff(3, 3^4, 1, 1);
assert valid_covering_set(U3_va4, E3_va4); //sufficient
assert valid_covering_set(E3_va4, U3_va4); //necessary
printf "valid and minimal covering set when v3(a) = 4\n\n";

printf "case v3(a) = 6\n";
E3_va6 := EtaleAlgebras3511Coeff(3, 3^6, 1, 1);
assert valid_covering_set(U3_va6, E3_va6); //sufficient
assert valid_covering_set(E3_va6, U3_va6); //necessary
printf "valid and minimal covering set when v3(a) = 6\n\n";

for a in [7,8,10] do
	printf "case v3(a) = %o\n", a;
	E3_va := EtaleAlgebras3511Coeff(3, 3^a, 1, 1);
	assert valid_covering_set(U3_va_7_8_10, E3_va); //sufficient
	assert valid_covering_set(E3_va, U3_va_7_8_10); //necessary
	printf "valid and minimal covering set when v3(a) = %o\n\n", a;
end for;

printf "case v3(a) = 9\n";
E3_va9 := EtaleAlgebras3511Coeff(3, 3^9, 1, 1);
assert valid_covering_set(U3_va9, E3_va9); //sufficient
assert valid_covering_set(E3_va9, U3_va9); //necessary
printf "valid and minimal covering set when v3(a) = 9\n\n";

printf "case v3(b) = 3\n";
E3_vb3 := EtaleAlgebras3511Coeff(3, 1, 3^3, 1);
assert valid_covering_set(U3_vb3, E3_vb3); //sufficient
assert valid_covering_set(E3_vb3, U3_vb3); //necessary
printf "valid and minimal covering set when v3(b) = 3\n\n";

printf "case v3(c) = 6\n";
E3_vc6 := EtaleAlgebras3511Coeff(3, 1, 1, 3^6);
assert valid_covering_set(U3_vc6, E3_vc6); //sufficient
assert valid_covering_set(E3_vc6, U3_vc6); //necessary
printf "valid and minimal covering set when v3(c) = 6\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 5\n";
printf "------------------------------------------------------------------\n\n";

printf "case v5(b) = 4\n";
E5_vb4 := EtaleAlgebras3511Coeff(5, 1, 5^4, 1);
assert valid_covering_set(U5_vb4, E5_vb4); //sufficient
assert valid_covering_set(E5_vb4, U5_vb4); //necessary
printf "valid and minimal covering set when v5(b) = 4\n\n";

printf "case v5(c) = 10\n";
E5_vc10 := EtaleAlgebras3511Coeff(5, 1, 1, 5^10);
assert valid_covering_set(U5_vc10, E5_vc10); //sufficient
assert valid_covering_set(E5_vc10, U5_vc10); //necessary
printf "valid and minimal covering set when v5(c) = 10\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 11\n";
printf "------------------------------------------------------------------\n\n";

printf "case v11(a) = 8\n";
E11_va8 := EtaleAlgebras3511Coeff(11, 11^8, 1, 1);
assert valid_covering_set(U11_va8, E11_va8); //sufficient
assert valid_covering_set(E11_va8, U11_va8); //necessary
printf "valid and minimal covering set when v11(a) = 8\n\n";

printf "case v11(b) = 4\n";
E11_vb4 := EtaleAlgebras3511Coeff(11, 1, 11^4, 1);
assert valid_covering_set(U11_vb4, E11_vb4); //sufficient
assert valid_covering_set(E11_vb4, U11_vb4); //necessary
printf "valid and minimal covering set when v11(b) = 4\n\n";

printf "done\n";
quit;