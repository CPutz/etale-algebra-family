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
    //f := &+[c[i] * x^(i-1) : i in [1..Rank(E)]];
    //coe := hom<PolynomialRing(BaseRing(E)) -> R | x>;
    //res := Resultant(coe(DefiningPolynomial(E)), y - f, x);
    //return UnivariatePolynomial(res);
end intrinsic;

intrinsic TschirnhausEliminate(E::EtAlg, i::RngElt, a::RngElt) -> SeqEnum
{Computes the Tschirnhaus transformations of the
defining polynomial of E and tries to eliminate the
first parameter using the coefficient of ai}
    T := Tschirnhaus(E);
    ai := Coefficient(T, Rank(E)-i);
    Rx := Parent(T);
    R := BaseRing(Rx);

    i := 1;
    while i lt Rank(E) do
        if Valuation(Content(Coefficient(ai, i, 1))) eq 0 then
            break;
        end if;
        i +:= 1;
    end while;
    printf "Eliminating %o\n", Name(R, i);

    S<[c]> := PolynomialRing(Q, Rank(E)-1);
    Sx<x> := PolynomialRing(S);
    f := hom<R -> Sx | Insert([Sx!S.i : i in [1..Rank(S)]], i, x)>;
    root := Roots(f(ai - a))[1][1];
    g := hom<R -> S  | Insert([S.i : i in [1..Rank(S)]], i, root)>;
    P, coeSx := ChangeRing(Rx, S, g);
    _, coeE := ChangeRing(P, PolynomialRing(BaseRing(E), Rank(E)-1));
    return coeE(coeSx(T));
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
    //C := [Zpx!Zx!c : c in Coefficients(T)];
    //C := [Zpx!Zx!c : c in Reverse(Prune(Coefficients(T)))];
    C := [Zpx!Zx!(nc[1] div p^nc[2]) : nc in Zip(Reverse(Prune(Coefficients(T))), N)];
    //Evaluation
    R := RSpace(Zp, Rank(E));
    //CE := {@ Evaluate(C, Eltseq(r)) : r in R | Evaluate(C[1], Eltseq(r)) in {0,1,2,3} @};
    CE := {@ Evaluate(C, Eltseq(r)) : r in R @};

    return rec< RC | congr := CE, exp := N>;
end intrinsic;

intrinsic GenerateCongruences(T::RngUPolElt, n::RngIntElt:
    N := NewtonOreExponents(T)) -> SeqEnum
{Generates a list of congruences on the coefficients mod p^n of
the minimal possible polynomials for E}
    R := BaseRing(T);
    p := UniformizingElement(BaseRing(R));
    Zp := Integers(Prime(BaseRing(R))^n);
    Zx<[c]>  := PolynomialRing(Z,  Rank(R));
    Zpx<[c]> := PolynomialRing(Zp, Rank(R));
    C := [Zpx!Zx!c : c in Coefficients(T)];
    //C := [Zpx!Zx!(nc[1] div p^nc[2]) : nc in Zip(Reverse(Prune(Coefficients(T))), N)];
    //Evaluation
    R := RSpace(Zp, Rank(R));
    //CE := {@ Evaluate(C, Eltseq(r)) : r in R | Evaluate(C[1], Eltseq(r)) in {0,1,2,3} @};
    CE := {@ Evaluate(C, Eltseq(r)) : r in R @};
    return CE;
end intrinsic;

intrinsic GenerateCongruencesElim(E::EtAlg, n::RngIntElt, as::SeqEnum[RngElt]) -> Rec
{}
    N := NewtonOreExponents(E);
    return {@ C : C in GenerateCongruences(TschirnhausEliminate(E, 1, a), n: N := N), a in as @};
end intrinsic;

intrinsic GenerateCongruences2(E::EtAlg, n::RngIntElt) -> SetIndx
{Generates a list of congruences on the coefficients mod p^n of
the minimal possible polynomials for E}
    T := Tschirnhaus(E);
    Zc<[c]> := PolynomialRing(Z, Rank(E));
    Zcx := PolynomialRing(Zc);
    FT := [<Parent(T)!F[1], F[2]> : F in Factorization(Zcx!T)];
    Zpx := PolynomialRing(Integers(Prime(BaseRing(E))^n));
    CF := [];
    for F in FT do
        F[1];
        C := GenerateCongruences(F[1], n);
        "done";
        C := [Zpx ! c : c in C];
        for i := 1 to F[2] do
            Append(~CF, C);
        end for;
    end for;
    CE := {@ &*TupSeq(c) : c in CartesianProduct(CF) @};
    return {@ Reverse(Prune(Coefficients(c))) : c in CE @};
end intrinsic;

intrinsic GenerateCongruences3(E::EtAlg, n::RngIntElt) -> SetIndx
{Generates a list of congruences on the coefficients mod p^n of
the minimal possible polynomials for E}
    FT := Factorization(DefiningPolynomial(E));
    if n eq 1 then
        Zpx := PolynomialRing(GF(Prime(BaseRing(E))));
    else
        Zpx := PolynomialRing(Integers(Prime(BaseRing(E))^n));
    end if;

    CF := [];
    for F in FT do
        T := Tschirnhaus(EtaleAlgebra(F[1]));
        C := GenerateCongruences(T, n);
        C := [Zpx ! c : c in C];
        for i := 1 to F[2] do
            Append(~CF, C);
        end for;
    end for;
    "done";
    CE := {@ &*TupSeq(c) : c in CartesianProduct(CF) @};
    return {@ Reverse(Prune(Coefficients(c))) : c in CE @};
end intrinsic;

intrinsic WriteCongruences(f::MonStgElt, C::SetIndx, N::SeqEnum[RngIntElt], p::RngIntElt)
{}
    exp := [p^n : n in N];
    R := CartesianProduct([Integers(e) : e in exp]);
    L := Sort({@ R!SeqTup(c) : c in C @});

    Write(f, exp: Overwrite := true);
    Write(f, "[");
    for l in L do
        Write(f, Sprintf("%o,", l));
    end for;
    Write(f, "]");
end intrinsic;

intrinsic GenerateCongruencesSquares(d::RngIntElt, D::RngIntElt, p::RngIntElt, n::RngIntElt) -> SetIndx
{Finds all polynomials of degree d such that its discriminant
is D upto squares modulo p^n}
    if n eq 1 then
        Zp := GF(p);
    else
        Zp := Integers(p^n);
    end if;
    Rc<[c]> := PolynomialRing(Zp, d);
    R := PolynomialRing(Rc);
    f := R!([c[d-i+1] : i in [1..d]] cat [1]);
    disc := Discriminant(f) * D;
    squares := {@ x^2 : x in Zp @};
    return {@ Eltseq(x) : x in RSpace(Zp, d) | Evaluate(disc, Eltseq(x)) in squares @};
end intrinsic;
