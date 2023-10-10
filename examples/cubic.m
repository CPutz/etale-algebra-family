AttachSpec("spec");

S<s> := PolynomialRing(Rationals());
_<t> := PolynomialRing(S);
F := t^3 - s*(t - 2);
//SetVerbose("AlgEtFam",2) to get additional verbose information
time E := EtaleAlgebraFamily(F, 3);
#E;