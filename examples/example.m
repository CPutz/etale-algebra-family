AttachSpec("spec");

S<s> := PolynomialRing(Rationals());
R<t> := PolynomialRing(S);
EtaleAlgebraFamily(t^2 - s, 2);
EtaleAlgebraFamily(t^3 - s, 3);