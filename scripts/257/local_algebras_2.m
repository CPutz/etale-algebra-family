// Load this file from the main folder
AttachSpec("spec");

K<a> := QuadraticField(21);

printf "\n==================================================================\n";
printf "We perform the computations from Proposition 5.34.\n";
printf "==================================================================\n\n";

R<t> := PolynomialRing(K);
F := t^5 * ((960 + 210*a)*t^2 + (-315 - 70*a)*t + (378 + 84*a)) / 9;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 5.35.\n";
printf "==================================================================\n\n";

p3 := Decomposition(K,3)[1,1];
E3 := EtaleAlgebras257Relative(p3);

assert #E3 eq 1;
printf "Found 1 local algebra at 3: %o\n", E3[1];