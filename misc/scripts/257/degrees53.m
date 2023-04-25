// Load this file from the main folder
AttachSpec("spec");

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

Q2 := pAdicField(2,500);
Q22 := UnramifiedExtension(Q2,2);
_<t> := PolynomialRing(Q2);
_<t2> := PolynomialRing(Q22);

U2 := [ EtaleAlgebra((t^5 - 2) * (t^3 - 2)),
	EtaleAlgebra(DefiningPolynomial(ext<Q22 | t2^4 + 2*t2^3 + 2*t2^2 + 2>,Q2)),
	DirectProduct(EtaleAlgebra(t^4 + 2*t^3 + 2*t^2 + 2),EtaleAlgebra(t^4 + 2*t^3 + 2*t^2 + 2)),
	EtaleAlgebra(t^8 + 2*t^7 + 2),
	EtaleAlgebra(t^8 + 2*t^7 + 6),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [6,2]]),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [3,3,1,1]]) ];

Q5 := pAdicField(5,500);
_<t> := PolynomialRing(Q5);

U5 := [
	EtaleAlgebra((t^4 - 5) * (t^2 - 10) * t * (t+1)),
	EtaleAlgebra((t^4 - 10) * (t^2 - 5) * t * (t+1)),
	EtaleAlgebra((t^4 + 10) * (t^2 - 5) * t * (t+1)) ] cat
  [ EtaleAlgebra((t^5 - 5*a*t + 5) * (t^2 - 10*a) * t) : a in [1,2,3] ] cat
  [ EtaleAlgebra((t^5 + 5*t + 5) * (t^2 - 10) * t),
	EtaleAlgebra((t^4 + 5) * (t^2 - 10) * t * (t+1)),
	EtaleAlgebra((t^6 - 5) * (t^2 - 10)),
	EtaleAlgebra((t^6 - 10) * (t^2 - 5)),
	EtaleAlgebra((t^7 - 5) * t) ];

Q7 := pAdicField(7,500);
_<t> := PolynomialRing(Q7);

U7 :=
  [ EtaleAlgebra((t^6 + a*7) * t * (t+1)) : a in [1,2,4] ] cat
  [ EtaleAlgebra((t^7 + 7*a*t + 7) * t) : a in [1,2,4] ] cat
  [ EtaleAlgebra((t^5 - 7) * (t^2 - 7) * t),
	EtaleAlgebra(t^8 - 7),
	EtaleAlgebra((t^6 + 7) * t * (t+1)),
	EtaleAlgebra((t^7 + 7*t + 7) * t) ];


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/fields_cubic_unramified257.m";
L3 := make_data();

printf "\nThere exist %o cubic number fields with signature (1,1) and unramfied outside 2, 5 and 7\n\n", #L3;

load "misc/scripts/257/fields_quintic_unramified257.m";
L5 := make_data();

printf "\nThere exist %o quintic number fields with signature (1,2) and unramfied outside 2, 5 and 7\n\n", #L5;


// Filter Ls for number fields that agree with the local data at 2 and 5
L3_filter := [ L : L in L3 |
	exists {E : E in U2 | contains_components_isomorphic_to(E, EtaleAlgebra(L,2)) } and
	exists {E : E in U5 | contains_components_isomorphic_to(E, EtaleAlgebra(L,5)) } and
	exists {E : E in U7 | contains_components_isomorphic_to(E, EtaleAlgebra(L,7)) } ];

printf "The following cubic number fields remain after checking local conditions at 2, 5 and 7: %o\n\n", L3_filter;

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
