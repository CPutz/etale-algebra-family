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
CtoCsigma := map < C -> Csigma | [(x1 + x2)*x3, x1*x2, x3^2] >;

printf "The quotient curve C/σ has genus %o\n", Genus(Csigma);

pt := Csigma![4,1,0];
assert not IsSingular(pt);

printf "It contains a non-singular point\n";

E0,CsigmatoE0 := EllipticCurve(Csigma, pt);
_,E0toCsigma := IsInvertible(CsigmatoE0);

E1 := EllipticCurve(x^3 - 154*x^2 + 6125*x);
_,E1toE0 := IsIsomorphic(E1,E0);
_,E0toE1 := IsIsomorphic(E0,E1);

printf "It is birational to the %o\n", E1;

E := EllipticCurve(x^3 - 7*x^2 - 49*x);
_,EtoE1 := IsIsogenous(E,E1);


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

//PhiE1 := Extend(Normalization(Expand(
//	Maps(E1, P1)!(E1toE0 * E0toCsigma * PhiCsigma))));
PhiE1 := map< E1 -> P1 |
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
assert PhiE1 eq E1toE0 * E0toCsigma * PhiCsigma;
