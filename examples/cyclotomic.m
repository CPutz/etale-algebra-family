AttachSpec("spec");

S<s> := PolynomialRing(Rationals());
R<t> := PolynomialRing(S);

//squares in Z_2
EtaleAlgebraFamily(t^2 - s, 2);

//cubes in Z_3
EtaleAlgebraFamily(t^3 - s, 3);