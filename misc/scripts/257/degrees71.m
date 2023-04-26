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
P2<x1,x2,x3> := ProjectiveSpace(QQ,2);

fC := ((4*s-1)*Evaluate(phi0,t) - (4*t-1)*Evaluate(phi0, s)) div (s - t);
C := Curve(P2, Homogenization(Evaluate(fC, [x1,x2,0,0]), x3));

printf "The curve C has genus %o\n", Genus(C);

S3 := Sym(3);
sigma := Automorphism(C, S3!(1,2));
Gsigma := AutomorphismGroup(C,[sigma]);
Csigma,CtoCsigma := CurveQuotient(Gsigma);

printf "The quotient curve C/σ has genus %o\n", Genus(Csigma);

E0,E0toCsigma := EllipticCurve()