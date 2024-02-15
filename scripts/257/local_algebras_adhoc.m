// Load this file from the main folder
AttachSpec("spec");

Z := Integers();
Q := Rationals();
_<x> := PolynomialRing(Q);

// Returns whether U is a valid covering set of isomorphism
// classes of etale algebras for L
function valid_covering_set(U,L);
	return forall (E) {E : E in L |
		exists {K : K in U | IsIsomorphic(E,K)}};
end function;


// Proposition B.1

printf "\n==================================================================\n";
printf "We perform the computations from Proposition A.1.\n";
printf "==================================================================\n\n";

Q2 := pAdicField(2,500);
Q22 := UnramifiedExtension(Q2,2);
_<t> := PolynomialRing(Q2);
_<t2> := PolynomialRing(Q22);

phi0 := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14);
phi1 := 10*t^4 + 4*t^3 + 2*t^2 + 2*t - 1;
phioo := 4*t - 1;

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
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [6,2]], Q2),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [3,3,1,1]], Q2) ];


// Compute parameter values for U2_1
B1 := [];
for r := 4 to 9 do
	// Perform computations over Q because it behaves more stable
	sep := Separant((5*x^4 + 4*x^3 + 4*x^2 + 8*x - 8)^2 - 2^(6 + 2*r) * (2*x - 1),2);
	prec := Max(0, Floor(sep - (6 + 2*r))) + 1;

	G,mG := UnitGroup(Integers(2^prec));
	for g in G do
		a := Z!mG(g);
		Append(~B1, 1 + a*2^(2*r));
	end for;
end for;

//Q2^* / (Q2^*)^2
G2,mG2 := pSelmerGroup(2,Q2);
for g in G2 do
	a := g@@mG2;
	if Valuation(a) mod 2 eq 0 then
		Append(~B1, 1 + a*2^(2*10));
	end if;
end for;

L2_1 := [EtaleAlgebra(phi0 - s * phioo) : s in B1];

// Check that U2_1 is a valid covering set for L2_1
assert valid_covering_set(U2_1, L2_1); //sufficient
assert valid_covering_set(L2_1, U2_1); //necessary
printf "valid covering set for S_{2,1}\n";


// Compute parameter values for U2_oo
Boo := [];
//r=1
G,mG := UnitGroup(Integers(2^8));
for g in G do
	a := Z!mG(g);
	Append(~Boo, a * 2^(-7));
end for;

L2_oo := [EtaleAlgebra(phi0 - s * phioo) : s in Boo];

// Check that U2_oo is a valid covering set for L2_oo
assert valid_covering_set(U2_oo, L2_oo); //sufficient
//assert valid_covering_set(L2_oo, U2_oo); //necessary
printf "valid covering set for S_{2,oo}\n\n";


// Proposition B.2

printf "\n==================================================================\n";
printf "We perform the computations from Proposition A.2.\n";
printf "==================================================================\n\n";

Q5 := pAdicField(5,500);
_<t> := PolynomialRing(Q5);

phi0 := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14);
phi1 := 10*t^4 + 4*t^3 + 2*t^2 + 2*t - 1;
phioo := 4*t - 1;

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


// Compute parameter values for U5_rest
G,mG := UnitGroup(Integers(5^3));
Brest := [Z!mG(g) : g in G | Z!mG(g) mod 5 ne 1];
L5_rest := [EtaleAlgebra(phi0 - s * phioo) : s in Brest];

// Check that U5_rest is a valid covering set for L5_rest
assert valid_covering_set(U5_rest, L5_rest); //sufficient
assert valid_covering_set(L5_rest, U5_rest); //necessary
printf "valid covering set for S_{5,rest}\n";


// Compute parameter values for U5_0
G,mG := UnitGroup(Integers(5^3));
B0 := [Z!mG(g) * 5^(5*r) : r in [1,2,3], g in G];
L5_0 := [EtaleAlgebra(phi0 - s * phioo) : s in B0];

// Check that U5_0 is a valid covering set for L5_0
assert valid_covering_set(U5_0, L5_0); //sufficient
assert valid_covering_set(L5_0, U5_0); //necessary
printf "valid covering set for S_{5,0}\n";


// Compute etale algebras for U5_1
L6s := [FieldOfFractions(L) : L in AllExtensions(Q5,6 : E := 6)];
L2s := [FieldOfFractions(L) : L in AllExtensions(Q5,2 : E := 2)];
L5_1 := [ E : L6 in L6s, L2 in L2s |
	IsPower(-7 * Discriminant(E),2) where E := EtaleAlgebra([L6,L2])];
L5_1_sample := [EtaleAlgebra(phi0 - (1 + 5^2*s) * phioo) : s in [1,2]];

// Check that U5_1 is a valid covering set for L5_1
assert valid_covering_set(U5_1, L5_1);
assert valid_covering_set(L5_1, U5_1);
assert valid_covering_set(U5_1, L5_1_sample);
assert valid_covering_set(L5_1_sample, U5_1);
printf "valid covering set for S_{5,1}\n";


// Compute etale algebras for U5_oo
L7s := [FieldOfFractions(L) : L in AllExtensions(Q5,7 : E := 7)];
L5_oo := [ EtaleAlgebra([L7,Q5]) : L7 in L7s ];
L5_oo_sample := [EtaleAlgebra(phi0 - 5^(-7)*s * phioo) : s in [1]];

// Check that U5_oo is a valid covering set for L5_oo
assert valid_covering_set(U5_oo, L5_oo);
assert valid_covering_set(L5_oo, U5_oo);
assert valid_covering_set(U5_oo, L5_oo_sample);
assert valid_covering_set(L5_oo_sample, U5_oo);
printf "valid covering set for S_{5,oo}\n\n";


printf "\n==================================================================\n";
printf "We perform the computations from Proposition A.3.\n";
printf "==================================================================\n\n";

Q7 := pAdicField(7,500);
_<t> := PolynomialRing(Q7);

phi0 := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14);
phi1 := 10*t^4 + 4*t^3 + 2*t^2 + 2*t - 1;
phioo := 4*t - 1;

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


// Compute parameter values for U7_rest
G,mG := UnitGroup(Integers(7^3));
Brest := [Z!mG(g) : g in G | Z!mG(g) mod 7 ne 1];
L7_rest := [EtaleAlgebra(phi0 - s * phioo) : s in Brest];

// Check that U7_rest is a valid covering set for L7_rest
assert valid_covering_set(U7_rest, L7_rest); //sufficient
assert valid_covering_set(L7_rest, U7_rest); //necessary
printf "valid covering set for S_{7,rest}\n";


// Compute etale algebras for U7_0
L5s := [FieldOfFractions(L) : L in AllExtensions(Q7,5 : E := 5)];
L2s := [FieldOfFractions(L) : L in AllExtensions(Q7,2 : E := 2)];
L7_0 := [ E : L5 in L5s, L2 in L2s |
	IsPower(-7 * Discriminant(E),2) where E := EtaleAlgebra([L5,L2,Q7])];
L7_0_sample := [EtaleAlgebra(phi0 - 7^5*s * phioo) : s in [1]];

// Check that U7_0 is a valid covering set for L7_0
assert valid_covering_set(U7_0, L7_0);
assert valid_covering_set(L7_0, U7_0);
assert valid_covering_set(U7_0, L7_0_sample);
assert valid_covering_set(L7_0_sample, U7_0);
printf "valid covering set for S_{7,0}\n";


// Compute etale algebras for U7_1
L8s := [FieldOfFractions(L) : L in AllExtensions(Q7,8 : E := 8)];
L7_1 := [ E : L8 in L8s |
	IsPower(-7 * Discriminant(E),2) where E := EtaleAlgebra([L8])];
L7_1_sample := [EtaleAlgebra(phi0 - (1 + 7^2*s) * phioo) : s in [1]];

// Check that U7_1 is a valid covering set for L7_1
assert valid_covering_set(U7_1, L7_1);
assert valid_covering_set(L7_1, U7_1);
assert valid_covering_set(U7_1, L7_1_sample);
assert valid_covering_set(L7_1_sample, U7_1);
printf "valid covering set for S_{7,1}\n";


// Compute parameter values for U7_oo
G,mG := UnitGroup(Integers(7^3));
Boo := [7^(-7*r) * Z!mG(g) : r in [1,2,3], g in G];
L7_oo := [EtaleAlgebra(phi0 - s * phioo) : s in Boo];

// Check that U7_oo is a valid covering set for L7_oo
assert valid_covering_set(U7_oo, L7_oo); //sufficient
assert valid_covering_set(L7_oo, U7_oo); //necessary
printf "valid covering set for S_{7,oo}\n";

printf "\ndone\n";
quit;