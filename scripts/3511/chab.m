SetEchoInput(true);

QQ := Rationals();
R<X> := PolynomialRing(QQ);
phi := (3*X^2 + X + 1)^5 * (1 - 5*X);

R<r,s,t,u,v,w> := PolynomialRing(QQ,6);
P<x1,x2,x3,x4> := ProjectiveSpace(QQ,3);

fs := [(Evaluate(phi,r) - Evaluate(phi, var)) div (r - var) : var in [s,t]];
G := [IsDivisibleBy(g,s-t) select (g div (s-t)) else g : g in GroebnerBasis(fs)];
D := Curve(P, [Homogenization(Evaluate(f, [x1,x2,x3,0,0,0]), x4) : f in G]);
I := ideal< R | G cat [u - (r + s + t), v - (r*s + r*t + s*t), w - r*s*t] >;
gs := [Homogenization(Evaluate(b, [0,0,0,x1,x2,x3]), x4) : b in Basis(EliminationIdeal(I,{u,v,w}))];
C := Curve(P, gs);
