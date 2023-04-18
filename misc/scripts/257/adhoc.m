//AttachSpec("spec");

Z := Integers();
Q := Rationals();
_<x> := PolynomialRing(Q);

// Proposition B.1

printf "==================================================================\n";
printf "We perform the computations from Proposition B.1.\n";
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
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [6,2]]),
	EtaleAlgebra([UnramifiedExtension(Q2,d) : d in [3,3,1,1]]) ];

// Compute parameter values for U2_1
B1 := [];
for r := 4 to 9 do
	// Perform computations over Q because it behaves more stable
	sep := Separant((5*x^4 + 4*x^3 + 4*x^2 + 8*x - 8)^2 - 2^(6 + 2*r) * (2*x-1),2);
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

// Check that U2_1 is a valid upper bound for L2_1
assert forall (E) {E : E in L2_1 | exists {K : K in U2_1 | IsIsomorphic(E,K)}};
printf "valid upper bound for S_{2,1}\n";

// Compute parameter values for U2_oo
Boo := [];
//r=1
G,mG := UnitGroup(Integers(2^8));
for g in G do
	a := Z!mG(g);
	Append(~Boo, a * 2^(-7));
end for;

L2_oo := [EtaleAlgebra(phi0 - s * phioo) : s in Boo];

// Check that U2_oo is a valid upper bound for L2_oo
assert forall (E) {E : E in L2_oo | exists {K : K in U2_oo | IsIsomorphic(E,K)}};
printf "valid upper bound for S_{2,oo}\n\n";

printf "done\n\n";