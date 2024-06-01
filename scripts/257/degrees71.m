// Load this file from the main folder
AttachSpec("spec");

function splitting_partition(E);
	return {* Degree(C[1],BaseRing(E)) ^^ C[2] : C in ComponentsIsoStructure(E) *};
end function;

// generates all subpartitions of p
function subpartitions(p);
	C := CartesianProduct([Partitions(r) : r in p]);
	return SetToSequence({@ {* r : r in ci, ci in c *} : c in C @});
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.16.\n";
printf "==================================================================\n\n";

load "scripts/257/covering_sets.dat";

E2 := [ E : E in U2 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Possible local algebra(s) at 2: %o\n", E2;
printf "Valuation of possible local discriminants at 2: %o\n",
	{ Valuation(Discriminant(E)) : E in E2 };

E5 := [ E : E in U5 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 5: %o\n",
	{ Valuation(Discriminant(E)) : E in E5 };

E7 := [ E : E in U7 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 7: %o\n",
	{ Valuation(Discriminant(E)) : E in E7 };


// A hunter search shows that the only septic number fields satisfying all
// local conditions, is Q(5^(1/7))


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.50.\n";
printf "==================================================================\n\n";

R<x> := PolynomialRing(Rationals());
E1 := EllipticCurve(x^3 - 7*x^2 - 49*x);
L<a> := NumberField(x^7 - 5);
E1L := BaseChange(E1,L);

Q1 := E1L![4*a^6 - a^5 - 4*a^4 + 4*a^3 + 4*a^2 - 5*a + 6,
		-15*a^6 - 12*a^5 + 24*a^4 - 6*a^3 - 51*a^2 + 25*a + 55,
		1];
Q2 := E1L![33*a^6 + 4*a^5 + 34*a^4 - 19*a^3 + 3*a^2 + 22*a - 9,
		119*a^6 - 28*a^5 + 56*a^4 - 91*a^3 + 77*a^2 + 154*a + 105,
		a^5 + 5*a^4 - 2*a^2 + a - 4];
Q3 := E1L![-42*a^6 - 21*a^5 + 77*a^4 - 98*a^2 + 91*a + 133,
		21*a^6 - 35*a^5 - 56*a^4 - 28*a^2 - 70*a + 70,
		8*a^6 + 2*a^5 - 20*a^4 + 24*a^2 - 19*a - 32];

S2 := TwoSelmerGroup(E1L);
assert Order(S2) eq 16; //implies rank <= 3
printf "Rank of E_1(L) is at most 3.\n";

assert IsLinearlyIndependent([Q1,Q2,Q3]);
assert forall { Q : Q in [Q1,Q2,Q3] | Order(Q) eq 0 };
printf "Q1, Q2, and Q3 are linearly independent points on E_1(L) of infinite order.\n";

printf "\ndone\n";
quit;