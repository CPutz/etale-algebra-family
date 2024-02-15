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
printf "valid and minimal covering set at the prime 2\n\n";


printf "\n==================================================================\n";
printf "We perform the computations for Proposition 6.12. \n";
printf "==================================================================\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";

Q3 := pAdicField(3,500);
_<t> := PolynomialRing(Q3);
Q32 := UnramifiedExtension(Q3,2);
_<t2> := PolynomialRing(Q32);
i := Roots(t^2 + 1, Q32)[1,1];

printf "case v3(a) = 4\n";
U3_va4 := [
	EtaleAlgebra(DefiningPolynomial(ext<Q32 | t2^3 + 3*i*t2 + 3>,Q3)
		* (t^4 + 2*t^3 + 2) * t),
	EtaleAlgebra((t^5 - 3) * (t^4 + 2*t^3 + 2) * t * (t+1)),
	EtaleAlgebra((t^3 + 3*t + 3) * (t^3 - 3*t + 3) * (t^4 + 2*t^3 + 2) * t)];
E3_va4 := EtaleAlgebras3511Coeff(3, 3^4, 1, 1);
assert valid_covering_set(U3_va4, E3_va4); //sufficient
assert valid_covering_set(E3_va4, U3_va4); //necessary
printf "valid and minimal covering set when v3(a) = 4\n\n";

E3_t5_3 := ext<Q3 | t^5 - 3>;

printf "case v3(a) = 6\n";
U3_va6 := [EtaleAlgebra(
	[E3_t5_3] cat [UnramifiedExtension(Q3,e) : e in es], Q3)
		: es in [[4,1,1],[3,2,1],[6]]];
E3_va6 := EtaleAlgebras3511Coeff(3, 3^6, 1, 1);
assert valid_covering_set(U3_va6, E3_va6); //sufficient
assert valid_covering_set(E3_va6, U3_va6); //necessary
printf "valid and minimal covering set when v3(a) = 6\n\n";

for a in [7,8,10] do
	printf "case v3(a) = %o\n", a;
	U3_va := [EtaleAlgebra([E3_t5_3, E3_t5_3, Q3],Q3)];
	E3_va := EtaleAlgebras3511Coeff(3, 3^a, 1, 1);
	assert valid_covering_set(U3_va, E3_va); //sufficient
	assert valid_covering_set(E3_va, U3_va); //necessary
	printf "valid and minimal covering set when v3(a) = %o\n\n", a;
end for;

printf "case v3(a) = 9\n";
U3_va9 := [EtaleAlgebra((t^5 - 3) * (t^4 + 2*t^3 + 2) * t * (t+1))];
E3_va9 := EtaleAlgebras3511Coeff(3, 3^9, 1, 1);
assert valid_covering_set(U3_va9, E3_va9); //sufficient
assert valid_covering_set(E3_va9, U3_va9); //necessary
printf "valid and minimal covering set when v3(a) = 9\n\n";

printf "case v3(b) = 3\n";
U3_vb3 := [
	EtaleAlgebra((t^5 - 3) * (t^2 - 3) * (t^2 + 3) * t * (t+1)),
	EtaleAlgebra((t^5 - 3) * (t^3 + 3*t + 3) * (t^2 - 3) * t)];
E3_vb3 := EtaleAlgebras3511Coeff(3, 1, 3^3, 1);
assert valid_covering_set(U3_vb3, E3_vb3); //sufficient
assert valid_covering_set(E3_vb3, U3_vb3); //necessary
printf "valid and minimal covering set when v3(b) = 3\n\n";

printf "case v3(c) = 6\n";
U3_vc6 := [EtaleAlgebra([UnramifiedExtension(Q3,e) : e in es], Q3)
		: es in [[5,5,1], [5,4,2], [7,3,1]]];
E3_vc6 := EtaleAlgebras3511Coeff(3, 1, 1, 3^6);
assert valid_covering_set(U3_vc6, E3_vc6); //sufficient
assert valid_covering_set(E3_vc6, U3_vc6); //necessary
printf "valid and minimal covering set when v3(c) = 6\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 5\n";
printf "------------------------------------------------------------------\n\n";

Q5 := pAdicField(5,500);
_<t> := PolynomialRing(Q5);

printf "case v5(b) = 4\n";
U5_vb4 := [EtaleAlgebra((t^5 + 10*t + 5) * (t^2 - 5) * (t^2 + 4*t + 2) * t * (t+1))];
E5_vb4 := EtaleAlgebras3511Coeff(5, 1, 5^4, 1);
assert valid_covering_set(U5_vb4, E5_vb4); //sufficient
assert valid_covering_set(E5_vb4, U5_vb4); //necessary
printf "valid and minimal covering set when v5(b) = 4\n\n";

printf "case v5(c) = 10\n";
U5_vc10 := [EtaleAlgebra([UnramifiedExtension(Q5,e) : e in es], Q5)
	: es in [[11], [7,3,1], [5,5,1], [5,4,2], [4,3,2,1,1]]];
E5_vc10 := EtaleAlgebras3511Coeff(5, 1, 1, 5^10);
assert valid_covering_set(U5_vc10, E5_vc10); //sufficient
assert valid_covering_set(E5_vc10, U5_vc10); //necessary
printf "valid and minimal covering set when v5(c) = 10\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 11\n";
printf "------------------------------------------------------------------\n\n";

Q11 := pAdicField(11,500);
_<t> := PolynomialRing(Q11);
Q11_5 := UnramifiedExtension(Q11,5);
_<t5> := PolynomialRing(Q11_5);

printf "case v11(a) = 8\n";
U11_va8 := [
	DirectProduct([EtaleAlgebra(t^2 + 11) : i in [1..5]] cat [EtaleAlgebra(t)]),
	EtaleAlgebra(DefiningPolynomial(ext<Q11_5 | t5^2 + 11>, Q11) * t)];
E11_va8 := EtaleAlgebras3511Coeff(11, 11^8, 1, 1);
assert valid_covering_set(U11_va8, E11_va8); //sufficient
assert valid_covering_set(E11_va8, U11_va8); //necessary
printf "valid and minimal covering set when v11(a) = 8\n\n";

printf "case v11(b) = 4\n";
U11_vb4 := [EtaleAlgebra([ext<Q11 | t^8 + 11>, UnramifiedExtension(Q11,2), Q11], Q11)];
E11_vb4 := EtaleAlgebras3511Coeff(11, 1, 11^4, 1);
assert valid_covering_set(U11_vb4, E11_vb4); //sufficient
assert valid_covering_set(E11_vb4, U11_vb4); //necessary
printf "valid and minimal covering set when v11(b) = 4\n\n";

printf "done\n";
quit;