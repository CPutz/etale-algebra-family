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

load "scripts/257/upperbounds.m";

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

load "scripts/257/covering.m";

QQ := Rationals();
_<x> := PolynomialRing(QQ);
L<a> := NumberField(x^7 - 5);

E1L := BaseChange(E1,L);
/*p1 := E1L!EtoE1(
	E(L)![4*a^6 - a^5 - 4*a^4 + 4*a^3 + 4*a^2 - 5*a + 6,
		-15*a^6 - 12*a^5 + 24*a^4 - 6*a^3 - 51*a^2 + 25*a + 55,
		1]);
p2 := E1L!EtoE1(
	E(L)![33*a^6 + 4*a^5 + 34*a^4 - 19*a^3 + 3*a^2 + 22*a - 9,
		119*a^6 - 28*a^5 + 56*a^4 - 91*a^3 + 77*a^2 + 154*a + 105,
		a^5 + 5*a^4 - 2*a^2 + a - 4]);
p3 := E1L!EtoE1(
	E(L)![-42*a^6 - 21*a^5 + 77*a^4 - 98*a^2 + 91*a + 133,
		21*a^6 - 35*a^5 - 56*a^4 - 28*a^2 - 70*a + 70,
		8*a^6 + 2*a^5 - 20*a^4 + 24*a^2 - 19*a - 32]);*/

p1 := E1L![
    1375 - 4625*a + 10625*a^2 - 10125*a^3 + 4275*a^4 + 400*a^5 - 1075*a^6,
    -24500 - 9625*a + 6125*a^2 + 24500*a^3 - 32725*a^4 + 12775*a^5 + 5425*a^6,
    79 - 30*a + 72*a^2 - 103*a^3 + 60*a^4 + 6*a^5 - 32*a^6];
p2 := E1L![
	1551325 + 855100*a + 1148900*a^2 + 903150*a^3 + 427450*a^4 + 436460*a^5 + 514295*a^6,
	1680300 + 4291900*a + 3332600*a^2 + 974100*a^3 + 1567800*a^4 + 2138565*a^5 + 650880*a^6,
	29373 + 13853*a + 15733*a^2 + 15483*a^3 + 7855*a^4 + 5686*a^5 + 8065*a^6];
p3 := E1L![
	-6221851330 - 958725725*a + 96640155*a^2 + 2344909765*a^3 - 80897335*a^4 - 804669505*a^5 - 1548935649*a^6,
	31290945 + 2486510950*a + 6751045280*a^2 + 2625740915*a^3 + 2269038590*a^4 - 837358970*a^5 - 796740539*a^6,
	-81216176 - 19566463*a - 5547447*a^2 + 28748216*a^3 - 170759*a^4 - 7249535*a^5 - 18585516*a^6];


/*p1 := E1L![
    -1075*a^6 + 400*a^5 + 4275*a^4 - 10125*a^3 + 10625*a^2 - 4625*a + 1375,
    5425*a^6 + 12775*a^5 - 32725*a^4 + 24500*a^3 + 6125*a^2 - 9625*a - 24500,
    -32*a^6 + 6*a^5 + 60*a^4 - 103*a^3 + 72*a^2 - 30*a + 79];
p2 := E1L![
    514295*a^6 + 436460*a^5 + 427450*a^4 + 903150*a^3 + 1148900*a^2 + 855100*a + 1551325,
    650880*a^6 + 2138565*a^5 + 1567800*a^4 + 974100*a^3 + 3332600*a^2 + 4291900*a + 1680300,
    8065*a^6 + 5686*a^5 + 7855*a^4 + 15483*a^3 + 15733*a^2 + 13853*a + 29373];
p3 := E1L![
    -1548935649*a^6 - 804669505*a^5 - 80897335*a^4 + 2344909765*a^3 + 96640155*a^2 - 958725725*a - 6221851330,
    -796740539*a^6 - 837358970*a^5 + 2269038590*a^4 + 2625740915*a^3 + 6751045280*a^2 + 2486510950*a + 31290945,
    -18585516*a^6 - 7249535*a^5 - 170759*a^4 + 28748216*a^3 - 5547447*a^2 - 19566463*a - 81216176];
*/

//time rank := RankBound(E1L); //crashes
// -> minimal model?
rank := 3;

gens := [p1,p2,p3];
assert IsLinearlyIndependent(gens); //crashes
assert #gens eq rank;

printf "We have a full-rank subgroup of E1(L)\n";

//the subgroup generated by gens is now saturated at 2 and 3
gens := Saturation(Saturation([E1L!p : p in gens], 2), 3);

A := AbelianGroup([Order(g) : g in gens]);
AtoE1L := map< A -> E1L | x :-> &+[Eltseq(x)[i]*gens[i] : i in [1..#gens]] >;
PhiE1L := map< E1L -> P1 | DefiningEquations(PhiE1) >;

printf "Performing elliptic curve Chabauty\n";

time V,R := Chabauty(AtoE1L, PhiE1L : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};

pts_E1L := { AtoE1L(v) : v in V };
printf "The points in E1(L) with rational image under Φ_E1 are %o\n", pts_E1L;

CL := BaseChange(C,L);
CLtoE1L := map< CL -> E1L | DefiningEquations(CtoCsigma * CsigmatoE0 * E0toE1) >;

assert BasePoints(CLtoE1L) eq {@ CL![0,0,1], CL![0,1,0], CL![1,0,0] @};

pts_CL := {@ @};
for p in pts_E1L do
	S := Cluster(E1L, p);
	pts_CL join:= RationalPoints(Pullback(CLtoE1L, S));
end for;

printf "The points in C(L) with rational image under ϕ are %o\n", pts_CL;