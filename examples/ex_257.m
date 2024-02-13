// Load this file from the main folder
AttachSpec("spec");

R<s> := PolynomialRing(Rationals());
_<t> := PolynomialRing(R);
F1 := (10*t^4 + 4*t^3 + 2*t^2 + 2*t - 1)^2 - s*(4*t - 1);
A1 := pAdicNbhdSpace(Rationals(), 5 : MinVal := 2, CongrVal := Integers(2)!0);
time E := EtaleAlgebraFamily(F1, 5 : ParameterSpace := A1, Precision := 200);
E;

ClearData(~E[1]);
ClearData(~E[2]);
[SimplifyToProduct(e) : e in E];