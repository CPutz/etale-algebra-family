// Load this file from the main folder
AttachSpec("spec");

load "scripts/257/upperbounds.m";

printf "\n==================================================================\n";
printf "We perform the computations from Theorem ?.\n";
printf "==================================================================\n\n";

R<t> := PolynomialRing(Rationals());
F8 := t^8 + 4*t^7 - 28*t^6 - 168*t^5 - 140*t^4 +560*t^3 + 840*t^2 - 480*t - 940;
L8 := NumberField(F8);

/*printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
time E2 := EtaleAlgebras257(2 : Simplify := false, Neighbourhoods := true);

L8_2 := EtaleAlgebra(L8,2);*/



printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";
time E3 := EtaleAlgebras257(3 : Simplify := false, Neighbourhoods := true);

L8_3 := EtaleAlgebra(L8,3);
assert exists (K3) { K3 : K3 in E3 | IsIsomorphic(K3,L8_3) };

Nbhds := Data(K3);
X := Universe(Nbhds);
K := AmbientSpace(X);

// 3 | z
N3z := Invert(pAdicNbhd(X, K!0, K!3, 1));
assert forall { N : N in Nbhds | N subset N3z };