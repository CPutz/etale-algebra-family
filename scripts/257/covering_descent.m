// Load this file from the main folder

printf "--- Warning ---\n";
printf "Page and theorem numbers mentioned below are currently not correct.\n";
printf "---------------\n\n";

printf "\n==================================================================\n";
printf "We construct the curves and maps from page 126.\n";
printf "==================================================================\n\n";

QQ := Rationals();
_<x> := PolynomialRing(QQ);
phi0 := 4*x^5*(25*x^3 + 20*x^2 + 14*x + 14);
phioo := 4*x - 1;

R<s,t,u,v> := PolynomialRing(QQ,4);
P1<y1,y2> := ProjectiveSpace(QQ,1);
P2<x1,x2,x3> := ProjectiveSpace(QQ,2);

fC := (Evaluate(phioo,s)*Evaluate(phi0,t) - Evaluate(phioo,t)*Evaluate(phi0, s)) div (s - t);
C := Curve(P2, Homogenization(Evaluate(fC, [x1,x2,0,0]), x3));

printf "The curve C has genus %o\n", Genus(C);

I := ideal< R | [fC, s + t - u, s*t - v] >;
fCsigma := Homogenization(Evaluate(Basis(EliminationIdeal(I,{u,v}))[1], [0,0,x1,x2]), x3);
Csigma := Curve(P2, fCsigma);
CtoCsigma := Extend(map < C -> Csigma | [(x1 + x2)*x3, x1*x2, x3^2] >);

printf "The quotient curve C/σ has genus %o\n", Genus(Csigma);

pt := Csigma![4,1,0];
assert not IsSingular(pt);

printf "It contains a non-singular point\n";

E0,CsigmatoE0 := EllipticCurve(Csigma, pt);
_,E0toCsigma := IsInvertible(CsigmatoE0);

E := EllipticCurve(x^3 - 154*x^2 + 6125*x);
_,EtoE0 := IsIsomorphic(E,E0);
_,E0toE := IsIsomorphic(E0,E);

printf "It is birational to the %o\n", E;

E1 := EllipticCurve(x^3 - 7*x^2 - 49*x);
_,E1toE := IsIsogenous(E1,E);

printf "Computing alternative equations for the map C/σ -> E\n";
CsigmatoE := Extend(Expand(CsigmatoE0 * E0toE));
_,EtoCsigma := IsInvertible(CsigmatoE);

//Descend Phi to E
Phi := map<C -> P1 |
    [CoordinateRing(C)!Homogenization(Evaluate(phi0, x1), x3),
     CoordinateRing(C)!Homogenization(Evaluate(phioo,x1), x3, 8)]>;

Phi1_st := (Evaluate(phioo,s)*Evaluate(phi0,t) + Evaluate(phioo,t)*Evaluate(phi0, s)) / 2;
Phi2_st := Evaluate(phioo,t) * Evaluate(phioo,s);
IPhi1 := ideal< R | [Phi1_st, s + t - u, s*t - v] >;
IPhi2 := ideal< R | [Phi2_st, s + t - u, s*t - v] >;
Phi1_uv := -50 * Homogenization(Evaluate(Basis(EliminationIdeal(IPhi1,{u,v}))[1], [0,0,x1,x2]), x3);
Phi2_uv := -4 * Homogenization(Evaluate(Basis(EliminationIdeal(IPhi2,{u,v}))[1], [0,0,x1,x2]), x3, 8);
PhiCsigma := map< Csigma -> P1 |
    [CoordinateRing(Csigma)!Phi1_uv,
     CoordinateRing(Csigma)!Phi2_uv] >;

// PhiCsigma is the descended map of Phi to Csigma
assert Phi eq CtoCsigma * PhiCsigma;

printf "Phi descends to C/σ\n";

//PhiE := Extend(Normalization(Expand(
//  Maps(E, P1)!(EtoCsigma * PhiCsigma))));
PhiE := map< E -> P1 |
    [-1/210739200000*x1^2*x2^8 - 1151/752640000*x1^2*x2^7*x3 - 619/15052800000*x1*x2^8*x3 - 
    1/1505280000*x2^9*x3 - 6901/1228800*x1^2*x2^6*x3^2 - 109997/268800000*x1*x2^7*x3^2 -
    68407/2007040000*x2^8*x3^2 + 150607841/153600000*x1^2*x2^5*x3^3 + 
    69430211/122880000*x1*x2^6*x3^3 - 2706337/823200000*x2^7*x3^3 + 
    11280882113/19200000*x1^2*x2^4*x3^4 - 283904059/3072000*x1*x2^5*x3^4 - 
    1742243819/268800000*x2^6*x3^4 - 1162793466037/5120000*x1^2*x2^3*x3^5 - 
    1776979726529/25600000*x1*x2^4*x3^5 + 103620140543/15360000*x2^5*x3^5 - 
    677047505633219/20480000*x1^2*x2^2*x3^6 + 997249111985861/30720000*x1*x2^3*x3^6 + 
    1045118570695493/614400000*x2^4*x3^6 + 148882850323777367/10240000*x1^2*x2*x3^7 +
    1049409335733094119/204800000*x1*x2^2*x3^7 - 2746994589364291/1920000*x2^3*x3^7 +
    1380981912101255666237/614400000*x1^2*x3^8 - 264434987424276053/122880*x1*x2*x3^8
    - 33709649407697573443/153600000*x2^2*x3^8 - 
    286343646031081741487/819200*x1*x3^9 + 1346385955810546875/16384*x2*x3^9 + 
    2748871326446533203125/196608*x3^10,
x1^2*x2^5*x3^3 + 1/42*x1*x2^6*x3^3 + 1/4116*x2^7*x3^3 + 5887/3*x1^2*x2^4*x3^4 + 
    605/3*x1*x2^5*x3^4 + 1835/84*x2^6*x3^4 - 95942/3*x1^2*x2^3*x3^5 - 557585/2*x1*x2^4*x3^5
    - 175781/12*x2^5*x3^5 - 273115122*x1^2*x2^2*x3^6 + 92100106/3*x1*x2^3*x3^6 + 
    172668097/12*x2^4*x3^6 + 123861484257*x1^2*x2*x3^7 + 78281706307/2*x1*x2^2*x3^7 - 
    15416657193/4*x2^3*x3^7 - 46813974955657/3*x1^2*x3^8 - 57406964906375/3*x1*x2*x3^8 
    - 15171859180457/12*x2^2*x3^8 + 4802336756156625/2*x1*x3^9 + 
    9159088134765625/12*x2*x3^9 - 1144886016845703125/12*x3^10] >;

// The equations above give a correct model for PhiE1
assert PhiE eq EtoCsigma * PhiCsigma;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.18.\n";
printf "==================================================================\n\n";

psi := CsigmatoE;
pi := CtoCsigma;

Bpsi := BaseScheme(psi);
Bpi := BaseScheme(pi);

Bpsi_pts,Lpsi := PointsOverSplittingField(Bpsi);
Bpi_pts,Lpi := PointsOverSplittingField(Bpi);

// pi is defined everywhere
assert #Bpi_pts eq 0;

for P in Bpsi_pts do
	B := Pullback(pi, P);
	pts,LP := PointsOverSplittingField(B);
	for p in pts do
		// we only consider the affine points of C
		if p[3] ne 0 then
			assert p eq C![0,0,1] or Phi(p) eq P1![1,1];
		end if;
	end for;
end for;

printf "psi ⚬ pi is only undefined for (0,0) and points (s,t) with Phi(s,t) = 1.\n";

G,GtoE := MordellWeilGroup(E);
EQ := [GtoE(g) : g in G];
printf "The Mordell-Weil group of E/Q is given by %o\n", EQ;

B := BaseScheme(pi * psi);
for P in EQ do
	C := Cluster(E,P);
	pts,LP := PointsOverSplittingField(Pullback(pi * psi, C));
	good_pts := [p : p in pts | p notin B and p[3] ne 0];

	for p in good_pts do
		assert
			Evaluate(x^2 - 7/20*x + 7/80, p[1] / p[3]) eq 0 and
			Evaluate(x^2 - 7/20*x + 7/80, p[2] / p[3]) eq 0;
	end for;
end for;

printf "The points of E(Q) lift to (affine) C(L) only if L contain Q(sqrt{-91}).\n";


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.19.\n";
printf "==================================================================\n\n";

L<a> := NumberField(x^7 - 5);

EL := BaseChange(E,L);
/*p1 := EL!E1toE(
	E1(L)![4*a^6 - a^5 - 4*a^4 + 4*a^3 + 4*a^2 - 5*a + 6,
		-15*a^6 - 12*a^5 + 24*a^4 - 6*a^3 - 51*a^2 + 25*a + 55,
		1]);
p2 := EL!E1toE(
	E1(L)![33*a^6 + 4*a^5 + 34*a^4 - 19*a^3 + 3*a^2 + 22*a - 9,
		119*a^6 - 28*a^5 + 56*a^4 - 91*a^3 + 77*a^2 + 154*a + 105,
		a^5 + 5*a^4 - 2*a^2 + a - 4]);
p3 := EL!E1toE(
	E1(L)![-42*a^6 - 21*a^5 + 77*a^4 - 98*a^2 + 91*a + 133,
		21*a^6 - 35*a^5 - 56*a^4 - 28*a^2 - 70*a + 70,
		8*a^6 + 2*a^5 - 20*a^4 + 24*a^2 - 19*a - 32]);*/

p1 := EL![
    1375 - 4625*a + 10625*a^2 - 10125*a^3 + 4275*a^4 + 400*a^5 - 1075*a^6,
    -24500 - 9625*a + 6125*a^2 + 24500*a^3 - 32725*a^4 + 12775*a^5 + 5425*a^6,
    79 - 30*a + 72*a^2 - 103*a^3 + 60*a^4 + 6*a^5 - 32*a^6];
p2 := EL![
	1551325 + 855100*a + 1148900*a^2 + 903150*a^3 + 427450*a^4 + 436460*a^5 + 514295*a^6,
	1680300 + 4291900*a + 3332600*a^2 + 974100*a^3 + 1567800*a^4 + 2138565*a^5 + 650880*a^6,
	29373 + 13853*a + 15733*a^2 + 15483*a^3 + 7855*a^4 + 5686*a^5 + 8065*a^6];
p3 := EL![
	-6221851330 - 958725725*a + 96640155*a^2 + 2344909765*a^3 - 80897335*a^4 - 804669505*a^5 - 1548935649*a^6,
	31290945 + 2486510950*a + 6751045280*a^2 + 2625740915*a^3 + 2269038590*a^4 - 837358970*a^5 - 796740539*a^6,
	-81216176 - 19566463*a - 5547447*a^2 + 28748216*a^3 - 170759*a^4 - 7249535*a^5 - 18585516*a^6];


//rank_bound := RankBound(EL);
rank_bound := 3;

assert rank_bound eq 3;

gens := [p1,p2,p3];
assert IsLinearlyIndependent(gens);
assert forall { p : p in [p1,p2,p3] | Order(p) eq 0 };
assert #gens eq rank_bound;

printf "We have a full-rank subgroup of E(L)\n";

gens cat:= [EL![0,0]];
//Saturation(G,n) saturates G at all primes <= n
assert SequenceToSet(Saturation([EL!p : p in gens], 3)) eq SequenceToSet(gens);

printf "The subgroup is saturated at 2 and 3\n";

printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.20.\n";
printf "==================================================================\n\n";

A := AbelianGroup([Order(g) : g in gens]);
AtoEL := map< A -> EL | x :-> &+[Eltseq(x)[i]*gens[i] : i in [1..#gens]] >;
PhiEL := map< EL -> P1 | DefiningEquations(PhiE) >;

printf "Performing elliptic curve Chabauty\n";

V,R := Chabauty(AtoEL, PhiEL : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};

pts_EL := { AtoEL(v) : v in V };
printf "The points in E(L) with rational image under Φ_E are %o\n", pts_EL;

assert pts_EL eq { EL![0,0,1], EL![0,1,0] };


printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.23.\n";
printf "==================================================================\n\n";

M := NumberField(x^3 + 4*x^2 + 14*x + 70); //generates 25x^3 + 20x^2 + 14x + 14
L := SplittingField(M);

printf "Computing a full-rank subgroup of the Mordell-Weil group of E over %o\n", L;

EL := BaseChange(E,L);
_,G,GtoEL := PseudoMordellWeilGroup(EL);

rankbound := RankBound(EL);
//rankbound := 2;
assert rankbound eq TorsionFreeRank(G);

printf "Found full-rank subgroup of E(L) (rank = %o)\n", TorsionFreeRank(G);

gens := [GtoEL(g) : g in Generators(G)];
//Saturation(G,n) saturates G at all primes <= n
sat23 := Saturation([EL!p : p in gens], 3);
A := AbelianGroup([Order(g) : g in sat23]);
AtoEL := map< A -> EL | a :-> &+[Eltseq(a)[i]*sat23[i] : i in [1..#sat23]] >;

printf "Constructed subgroup which is saturated at 2 and 3.\n";

printf "Performing elliptic curve Chabauty\n";

PhiEL := map< EL -> P1 | DefiningEquations(PhiE) >;

V,R := Chabauty(AtoEL, PhiEL : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};


pts_EL := { AtoEL(v) : v in V };
printf "The points in E(L) with rational image under Φ_E are %o\n", pts_EL;

assert forall { p : p in pts_EL |
	(p[1] in QQ and p[2] in QQ and p[3] in QQ) or
	PhiEL(p) eq P1![0,1] };

printf "All points of E(L) - E(Q) map to (0 : 1) under Φ_E.\n";

printf "\n==================================================================\n";
printf "We perform the computations from Proposition 4.30.\n";
printf "==================================================================\n\n";

L := NumberField(x^4 - 2*x^3 - 2*x^2 - 4*x - 10);

printf "Computing a full-rank subgroup of the Mordell-Weil group of E over %o\n", L;

EL := BaseChange(E,L);
_,G,GtoEL := PseudoMordellWeilGroup(EL);

rankbound := RankBound(EL);
//rankbound := 2;
assert rankbound eq TorsionFreeRank(G);

print "Found full-rank subgroup of E(L) (rank = %o)\n", TorsionFreeRank(G);

gens := [GtoEL(g) : g in Generators(G)];
//Saturation(G,n) saturates G at all primes <= n
sat23 := Saturation([EL!p : p in gens], 3);
A := AbelianGroup([Order(g) : g in sat23]);
AtoEL := map< A -> EL | x :-> &+[Eltseq(x)[i]*sat23[i] : i in [1..#sat23]] >;

printf "Constructed subgroup which is saturated at 2 and 3.\n";

printf "Performing elliptic curve Chabauty\n";

PhiEL := map< EL -> P1 | DefiningEquations(PhiE) >;

V,R := Chabauty(AtoEL, PhiEL : IndexBound := 6);
assert R lt Infinity();
assert PrimeDivisors(R) subset {2,3};


pts_EL := { AtoEL(v) : v in V };
printf "The points in E(L) with rational image under Φ_E are %o\n", pts_EL;

CL := BaseChange(C,L);
CLtoEL := map< CL -> EL | DefiningEquations(CtoCsigma * CsigmatoE0 * E0toE) >;

pts_CL := {@ @};
for p in pts_EL do
	S := Cluster(EL, p);
	pts_CL join:= RationalPoints(Pullback(CLtoEL, S));
end for;

printf "The points in C(L) with rational image under ϕ are %o\n", pts_CL;

printf "\ndone\n";
quit;