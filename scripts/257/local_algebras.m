// Load this file from the main folder
AttachSpec("spec");

// Returns whether U is a valid upper bound of isomorphism
// classes of etale algebras for L
function valid_upper_bound(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;

printf "\n==================================================================\n";
printf "We perform the computations from Theorem 5.7.\n";
printf "==================================================================\n\n";

SetVerbose("AlgEtFam",1);

Q2 := pAdicField(2,500);
Q22 := UnramifiedExtension(Q2,2);
_<t> := PolynomialRing(Q2);
_<t2> := PolynomialRing(Q22);

// Upper bounds
U2_0 := [ EtaleAlgebra((t^5 - 2) * (t^3 - 2)) ];
U2_1 := [
	EtaleAlgebra(DefiningPolynomial(ext<Q22 | t2^4 + 2*t2^3 + 2*t2^2 + 2>,Q2)),
	DirectProduct(EtaleAlgebra(t^4 + 2*t^3 + 2*t^2 + 2),EtaleAlgebra(t^4 + 2*t^3 + 2*t^2 + 2)),
	EtaleAlgebra(t^8 + 2*t^7 + 2),
	EtaleAlgebra(t^8 + 2*t^7 + 6) ];
U2_oo := [
	EtaleAlgebra(t^8 + 2*t^7 + 2),
	EtaleAlgebra(t^8 + 2*t^7 + 6),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [6,2]]),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [3,3,1,1]]) ];
U2 := U2_0 cat U2_1 cat U2_oo;

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
time E2 := EtaleAlgebras257(2 : Simplify := false);

assert valid_upper_bound(U2, E2); //sufficient
assert valid_upper_bound(E2, U2); //necessary
printf "valid upper bound the prime 2\n\n";


Q3 := pAdicField(3,500);

// Upper bound
U3 := [ EtaleAlgebra([UnramifiedExtension(Q3,d) : d in P]) :
	P in [[8],[6,1,1],[5,2,1],[4,3,1]] ];

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";
time E3 := EtaleAlgebras257(3 : Simplify := false);

assert valid_upper_bound(U3, E3); //sufficient
assert valid_upper_bound(E3, U3); //necessary
printf "valid upper bound the prime 3\n\n";


Q5 := pAdicField(5,500);
_<t> := PolynomialRing(Q5);

// Upper bounds
U5_rest := [
	EtaleAlgebra((t^4 - 5) * (t^2 - 10) * t * (t+1)),
	EtaleAlgebra((t^4 - 10) * (t^2 - 5) * t * (t+1)),
	EtaleAlgebra((t^4 + 10) * (t^2 - 5) * t * (t+1)) ] cat
  [ EtaleAlgebra((t^5 - 5*a*t + 5) * (t^2 - 10*a) * t) : a in [1,2,3] ];
U5_0 := [
	EtaleAlgebra((t^5 + 5*t + 5) * (t^2 - 10) * t),
	EtaleAlgebra((t^4 + 5) * (t^2 - 10) * t * (t+1)) ];
U5_1 := [
	EtaleAlgebra((t^6 - 5) * (t^2 - 10)),
	EtaleAlgebra((t^6 - 10) * (t^2 - 5)) ];
U5_oo := [
	EtaleAlgebra((t^7 - 5) * t) ];
U5 := U5_rest cat U5_0 cat U5_1 cat U5_oo;

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 5\n";
printf "------------------------------------------------------------------\n\n";
time E5 := EtaleAlgebras257(5 : Simplify := false);

assert valid_upper_bound(U5, E5); //sufficient
assert valid_upper_bound(E5, U5); //necessary
printf "valid upper bound the prime 5\n\n";


Q7 := pAdicField(7,500);
_<t> := PolynomialRing(Q7);

// Upper bounds
U7_rest :=
	 [ EtaleAlgebra((t^6 + a*7) * t * (t+1)) : a in [1,2,4] ]
 cat [ EtaleAlgebra((t^7 + 7*a*t + 7) * t) : a in [1,2,4] ];
U7_0 := [
	EtaleAlgebra((t^5 - 7) * (t^2 - 7) * t) ];
U7_1 := [
	EtaleAlgebra(t^8 - 7) ];
U7_oo := [
	EtaleAlgebra((t^6 + 7) * t * (t+1)),
	EtaleAlgebra((t^7 + 7*t + 7) * t) ];
U7 := U7_rest cat U7_0 cat U7_1 cat U7_oo;

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 7\n";
printf "------------------------------------------------------------------\n\n";
time E7 := EtaleAlgebras257(7 : Simplify := false);

assert valid_upper_bound(U7, E7); //sufficient
assert valid_upper_bound(E7, U7); //necessary
printf "valid upper bound the prime 7\n\n";

printf "done\n";