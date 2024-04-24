// Load this file from the main folder
AttachSpec("spec");

printf "--- Warning ---\n";
printf "Page and theorem numbers mentioned below are currently not correct.\n";
printf "---------------\n\n";

load "scripts/257/covering_sets.dat";

printf "\n==================================================================\n";
printf "We perform the computations from Theorem 5.29.\n";
printf "==================================================================\n\n";

R<t> := PolynomialRing(Rationals());
F8 := t^8 + 4*t^7 - 28*t^6 - 168*t^5 - 140*t^4 +560*t^3 + 840*t^2 - 480*t - 940;
L8 := NumberField(F8);

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 2\n";
printf "------------------------------------------------------------------\n\n";
E2 := EtaleAlgebras257(2 : Simplify := false, Neighbourhoods := true);

L8_2 := EtaleAlgebra(L8,2);
assert exists (K2) { K2 : K2 in E2 | IsIsomorphic(K2,L8_2) };

Nbhds := Data(K2);
X := Universe(Nbhds);
K := AmbientSpace(X);

//2 | y and (eta(x) = 13 mod 32 or z = 7 (mod 8))  or 2 || z
assert forall { N : N in Nbhds |
	N subset pAdicNbhd(X, K!1 + 3*2^2, K!2^5, 1) or N subset pAdicNbhd(X, K!1, 7*K!2^2, 2) or
	(N subset Invert(pAdicNbhd(X, K!0, K!2^7, 1)) and not N subset Invert(pAdicNbhd(X, K!0, K!2^14, 1)))
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 2\n\n";

printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 3\n";
printf "------------------------------------------------------------------\n\n";
E3 := EtaleAlgebras257(3 : Simplify := false, Neighbourhoods := true);

L8_3 := EtaleAlgebra(L8,3);
assert exists (K3) { K3 : K3 in E3 | IsIsomorphic(K3,L8_3) };

Nbhds := Data(K3);
X := Universe(Nbhds);
K := AmbientSpace(X);

// 3 | z
assert forall { N : N in Nbhds |
	N subset Invert(pAdicNbhd(X, K!0, K!3^7, 1))
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 3\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 5\n";
printf "------------------------------------------------------------------\n\n";
E5 := EtaleAlgebras257(5 : Simplify := false, Neighbourhoods := true);

L8_5 := EtaleAlgebra(L8,5);
assert exists (K5) { K5 : K5 in E5 | IsIsomorphic(K5,L8_5) };

Nbhds := Data(K5);
X := Universe(Nbhds);
K := AmbientSpace(X);

// 5 | x
assert forall { N : N in Nbhds |
	N subset pAdicNbhd(X, K!0, K!5^5, 1)
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 5\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 7\n";
printf "------------------------------------------------------------------\n\n";
E7 := EtaleAlgebras257(7 : Simplify := false, Neighbourhoods := true);

L8_7 := EtaleAlgebra(L8,7);
assert exists (K7) { K7 : K7 in E7 | IsIsomorphic(K7,L8_7) };

Nbhds := Data(K7);
X := Universe(Nbhds);
K := AmbientSpace(X);

// eta(x) = 4 mod 7 and eta(x) != 32 mod 49 or 7 | z
assert forall { N : N in Nbhds |
	(N subset pAdicNbhd(X, K!4, K!7, 1) and not N subset pAdicNbhd(X, K!32, K!49, 1)) or
	N subset Invert(pAdicNbhd(X, K!0, K!7^7, 1))
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 7\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 11\n";
printf "------------------------------------------------------------------\n\n";
E11 := EtaleAlgebras257(11 : Simplify := false, Neighbourhoods := true);

L8_11 := EtaleAlgebra(L8,11);
assert exists (K11) { K11 : K11 in E11 | IsIsomorphic(K11,L8_11) };

Nbhds := Data(K11);
X := Universe(Nbhds);
K := AmbientSpace(X);

// eta(x) = 7 mod 11
assert forall { N : N in Nbhds |
	N subset pAdicNbhd(X, K!7, K!11, 1)
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 11\n\n";


printf "------------------------------------------------------------------\n";
printf "performing computations for the prime 197\n";
printf "------------------------------------------------------------------\n\n";
E197 := EtaleAlgebras257(197 : Simplify := false, Neighbourhoods := true);

L8_197 := EtaleAlgebra(L8,197);
assert exists (K197) { K197 : K197 in E197 | IsIsomorphic(K197,L8_197) };

Nbhds := Data(K197);
X := Universe(Nbhds);
K := AmbientSpace(X);

// eta(x) = 177 mod 197
assert forall { N : N in Nbhds |
	N subset pAdicNbhd(X, K!177, K!197, 1)
	where K := AmbientSpace(X) where X := Parent(N)};
printf "Result verified for 197\n\n";

printf "\ndone\n";
quit;