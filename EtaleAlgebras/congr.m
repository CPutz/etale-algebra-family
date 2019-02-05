//Constants
Z := Integers();
Q := Rationals();
RC := recformat< congr : SetIndx, exp : SeqEnum >;

intrinsic Tschirnhaus(E::EtAlg) -> SeqEnum
{Computes all Tschirnhaus transformations of the
defining polynomial of E}
    C<[c]> := PolynomialRing(BaseRing(E), Rank(E));
    R<x, y> := PolynomialRing(C, 2);
    Eis := [Ei[1] : j in [1..Ei[2]], Ei in Components(E)];
    vs := Partition([c[i] : i in [1..Rank(E)]], [AbsoluteDegree(Ei) : Ei in Eis]);
    fs := [&+[v[i] * x^(i-1) : i in [1..#v]] : v in vs];
    coe := hom<PolynomialRing(BaseRing(E)) -> R | x>;
    res := &*[Resultant(coe(DefiningPolynomial(Eif[1])), y - Eif[2], x) : Eif in Zip(Eis, fs)];
    return UnivariatePolynomial(res);
end intrinsic;

intrinsic TschirnhausEliminate(E::EtAlg) -> SeqEnum
{Computes the Tschirnhaus transformations of the
defining polynomial of E and tries to eliminate the\
first parameter using the coefficient of a1}
    T := Tschirnhaus(E);
    a1 := Coefficient(T, Rank(E)-1);
    R := Parent(a1);
    S<[c]> := PolynomialRing(Q, Rank(E)-1);
    Sx<x> := PolynomialRing(S);
    f := hom<R -> Sx | [x] cat [S.i : i in [1..Rank(S)]]>;
    root := Roots(f(a1))[1][1];
    g := hom<R -> S  | [root] cat [S.i : i in [1..Rank(S)]]>;
    T2 := ChangeRing(T, S, g);
    return ChangeRing(T2, BaseRing(E));
end intrinsic;

intrinsic NewtonOreExponents(E::EtAlg) -> SeqEnum[RngIntElt]
{Returns the minimal valuation of every coefficient
over all minimal polynomials for E}
    return NewtonOreExponents(Tschirnhaus(E));
end intrinsic;

intrinsic NewtonOreExponents(T::RngUPolElt) -> SeqEnum[RngIntElt]
{Returns the minimal valuation of every coefficient of T}
    return Reverse([Valuation(Content(c)) : c in Prune(Coefficients(T))]);
end intrinsic;

intrinsic GenerateCongruences(E::EtAlg, n::RngIntElt) -> Rec
{Generates a list of congruences on the coefficients mod p of
the minimal possible polynomials for E}
    T := Tschirnhaus(E);
    N := NewtonOreExponents(T);
    p := UniformizingElement(BaseRing(E));
    Zp := Integers(Prime(BaseRing(E))^n);
    Zx<[c]>  := PolynomialRing(Z,  Rank(E));
    Zpx<[c]> := PolynomialRing(Zp, Rank(E));
    C := [Zpx!Zx!(nc[1] div p^nc[2]) : nc in Zip(Reverse(Prune(Coefficients(T))), N)];
    //Evaluation
    R := RSpace(Zp, Rank(E));
    //CE := {@ Evaluate(C, Eltseq(r)) : r in R | Evaluate(C[1], Eltseq(r)) in {0,1,2,3} @};
    CE := {@ Evaluate(C, Eltseq(r)) : r in R @};
    return rec< RC | congr := CE, exp := N>;
end intrinsic;

intrinsic GenerateCongruences(T::RngUPolElt, n::RngIntElt) -> SeqEnum
{Generates a list of congruences on the coefficients mod p of
the minimal possible polynomials for E}
    R := BaseRing(T);
    N := NewtonOreExponents(T);
    p := UniformizingElement(BaseRing(R));
    Zp := Integers(Prime(BaseRing(R))^n);
    Zx<[c]>  := PolynomialRing(Z,  Rank(R));
    Zpx<[c]> := PolynomialRing(Zp, Rank(R));
    C := [Zpx!Zx!c : c in Coefficients(T)];
    //Evaluation
    R := RSpace(Zp, Rank(R));
    //CE := {@ Evaluate(C, Eltseq(r)) : r in R | Evaluate(C[1], Eltseq(r)) in {0,1,2,3} @};
    CE := {@ Evaluate(C, Eltseq(r)) : r in R @};
    return CE;
end intrinsic;

intrinsic GenerateCongruences2(E::EtAlg, n::RngIntElt) -> Rec
{Generates a list of congruences on the coefficients mod p of
the minimal possible polynomials for E}
    T := Tschirnhaus(E);
    Zc<[c]> := PolynomialRing(Z, Rank(E));
    Zcx := PolynomialRing(Zc);
    FT := [<Parent(T)!F[1], F[2]> : F in Factorization(Zcx!T)];
    CF := [];
    Zp := Integers(Prime(BaseRing(E))^n);
    Zpx := PolynomialRing(Zp);
    CF := [];
    for F in FT do
        C := GenerateCongruences(F[1], n);
        C := [(Zpx ! c)^F[2] : c in C];
        Append(~CF, C);
    end for;
    [#c : c in CF];
    CE := {@ &*TupSeq(c) : c in CartesianProduct(CF) @};
    return {@ Reverse(Prune(Coefficients(c))) : c in CE @};
end intrinsic;