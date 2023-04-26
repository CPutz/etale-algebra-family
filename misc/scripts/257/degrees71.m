// Load this file from the main folder
AttachSpec("spec");


function splitting_partition(E);
	return {* Degree(C[1],BaseRing(E)) ^^ C[2] : C in ComponentsIsoStructure(E) *};
end function;

// generates all subpartitions of p
function subpartitions(p);
	C := CartesianProduct([Partitions(r) : r in p]);
	return SetToSequence({@ {* r : r in ci, ci in c *} : c in C @});
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/upperbounds.m";

E2 := [ E : E in U2 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Possible local algebra(s) at 2: %o\n", E2;
printf "Valuation of possible local discriminants at 2: %o\n",
	{ Valuation(Discriminant(E)) : E in E2 };

E5 := [ E : E in U5 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 5: %o\n",
	{ Valuation(Discriminant(E)) : E in E5 };

E7 := [ E : E in U7 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 7: %o\n",
	{ Valuation(Discriminant(E)) : E in E7 };


// A hunter search shows that the only septic number fields satisfying all
// local conditions, is Q(5^(1/7))

printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

QQ := Rationals();
_<x> := PolynomialRing(QQ);
L<a> := NumberField(x^7 - 5);
phi0 := 4*x^5*(25*x^3 + 20*x^2 + 14*x + 14);

_<s,t,u,v> := PolynomialRing(QQ,4);
P1 := ProjectiveSpace(QQ,1);
P2<x1,x2,x3> := ProjectiveSpace(QQ,2);

fC := ((4*s-1)*Evaluate(phi0,t) - (4*t-1)*Evaluate(phi0, s)) div (s - t);
C := Curve(P2, Homogenization(Evaluate(fC, [x1,x2,0,0]), x3));

printf "The curve C has genus %o\n", Genus(C);

S3 := Sym(3);
sigma := Automorphism(C, S3!(1,2));
Gsigma := AutomorphismGroup(C,[sigma]);
Csigma,CtoCsigma := CurveQuotient(Gsigma);

printf "The quotient curve C/σ has genus %o\n", Genus(Csigma);

pt := Csigma![1,1,0,0];
assert not IsSingular(pt);

printf "It contains a non-singular point\n";

E0,E0toCsigma := EllipticCurve(Csigma, Csigma![1,1,0,0]);

E1 := EllipticCurve(x^3 - 154*x^2 + 6125*x);
_,E1toE0 := IsIsomorphic(E1,E0);

E := EllipticCurve(x^3 - 7*x^2 - 49*x);
_,EtoE1 := IsIsogenous(E,E1);

p1 := EtoE1(
	E(L)![4*a^6 - a^5 - 4*a^4 + 4*a^3 + 4*a^2 - 5*a + 6,
		-15*a^6 - 12*a^5 + 24*a^4 - 6*a^3 - 51*a^2 + 25*a + 55,
		1]);
p2 := EtoE1(
	E(L)![33*a^6 + 4*a^5 + 34*a^4 - 19*a^3 + 3*a^2 + 22*a - 9,
		119*a^6 - 28*a^5 + 56*a^4 - 91*a^3 + 77*a^2 + 154*a + 105,
		a^5 + 5*a^4 - 2*a^2 + a - 4]);
p3 :=EtoE1(
	E(L)![-42*a^6 - 21*a^5 + 77*a^4 - 98*a^2 + 91*a + 133,
		21*a^6 - 35*a^5 - 56*a^4 - 28*a^2 - 70*a + 70,
		8*a^6 + 2*a^5 - 20*a^4 + 24*a^2 - 19*a - 32]);

