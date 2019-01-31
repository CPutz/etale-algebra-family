//Constants
Z := Integers();

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

intrinsic NewtonOreExponents(E::EtAlg: T := Tschirnhaus(E)) -> SeqEnum[RngIntElt]
{Returns the minimal valuation of every coefficient
over all minimal polynomials for E}
    return Reverse([Valuation(Content(c)) : c in Prune(Coefficients(T))]);
end intrinsic;

intrinsic GenerateCongruences(E::EtAlg) -> Tup
{Generates a list of congruences on the coefficients mod p of
the minimal possible polynomials for E}
    T := Tschirnhaus(E);
    N := NewtonOreExponents(E: T := T);
    p := UniformizingElement(BaseRing(E));
    Zx<[c]> := PolynomialRing(Z, Rank(E));
    C := [Zx!(nc[1] div p^nc[2]) : nc in Zip(Reverse(Prune(Coefficients(T))), N)];
    //Evaluation
    R := RSpace(Integers(Prime(BaseRing(E))), Rank(E));
    CE := {@ Evaluate(C, Eltseq(r)) : r in R @};
    return <CE, N>;
end intrinsic;