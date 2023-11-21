Z := Integers();
Q := Rationals();

intrinsic MonogenicGenerator(K::FldPad, B::FldPad) -> FldPadElt
{Gives a generator of O_K, i.e. a in K such that O_K = O_B[a]}
    f := InertiaDegree(K,B);
    U := UnramifiedExtension(B,f);
    fU := DefiningPolynomial(U);

    th := Roots(fU,K)[1,1];
    a := UniformizingElement(K);

    fmin := MinimalPolynomial(a + th, B);
    //a + th generates O_K
    assert IsIntegral(th) and IsIntegral(a);
    assert Valuation(Discriminant(fmin)) eq Valuation(Discriminant(Integers(K),Integers(B)));

    return a + th;
end intrinsic;

intrinsic Tschirnhaus(E::AlgEtpAdic, f::Map) -> RngUPolElt
{Computes a Tschirnhaus generating polynomial for O_E/O_B with
coefficients in Codomain(f) along the f : B -> C}
    B := BaseRing(E);
    C := Codomain(f);
    Cstruc := ComponentsIsoStructure(E);

    fmins := [<MinimalPolynomial(MonogenicGenerator(Ci[1],B),B), Ci[2]>
        : Ci in Cstruc];

    RC := PolynomialRing(C);
    phi := hom<PolynomialRing(B) -> RC | f,RC.1>;
    Rc<[c]> := PolynomialRing(C, Dimension(E));
    R<x, y> := PolynomialRing(Rc, 2);
    S<t> := PolynomialRing(Rc);
    tsch := S!1;

    i := 1;
    for fs in fmins do
        for k := 1 to fs[2] do
            g := Evaluate(phi(fs[1]), x);
            res := Resultant(g, y - &+[c[i + j] * x^j : j in [0..Degree(g)-1]],x);
            tsch *:= Evaluate(res, [0,t]);
            i +:= Degree(g);
        end for;
    end for;

    return tsch;
end intrinsic;

intrinsic Tschirnhaus(E::AlgEtpAdic) -> RngUPolElt
{Computes a Tschirnhaus generating polynomial for O_E/O_B}
    B := BaseRing(E);
    return Tschirnhaus(E, hom<B -> B | x :-> x>);
end intrinsic;

intrinsic Tschirnhaus(K::FldPad, B::FldPad, f::Map) -> RngUPolElt
{Computes a Tschirnhaus generating polynomial for O_K/O_B with
coefficients in Codomain(f) along the f : B -> C}
    C := Codomain(f);

    fmin := MinimalPolynomial(MonogenicGenerator(K,B),B);

    RC := PolynomialRing(C);
    phi := hom<PolynomialRing(B) -> RC | f,RC.1>;
    Rc<[c]> := PolynomialRing(C, Degree(fmin));
    R<x, y> := PolynomialRing(Rc, 2);
    S<t> := PolynomialRing(Rc);

    g := Evaluate(phi(fmin), x);
    res := Resultant(g, y - &+[c[j] * x^j : j in [1..Degree(g)]],x);
    return Evaluate(res, [0,t]);
end intrinsic;

intrinsic ComputeCongruences(E::AlgEtpAdic, k::RngIntElt) -> SeqEnum
{Computes the defining polynomials of O_E/O_B modulo p^k,
where p is a uniformizer of E}
    B := BaseRing(E);
    assert InertiaDegree(B) eq 1;

    p := Prime(B);
    if k eq 1 then
        C := GF(p);
    else
        C := Integers(p^k);
    end if;
    phi := map<B -> C | x :-> C!Z!x>;

    Cstruc := ComponentsIsoStructure(E);
    RC := PolynomialRing(C);
    Tschs := [];
    for Ci in Cstruc do
        tsch := Tschirnhaus(Ci[1], B, phi);
        tsch_coeff := Coefficients(tsch);
        R := RSpace(C, Degree(tsch));
        congrs := SetToSequence({@ RC![Evaluate(c, Eltseq(r))
            : c in tsch_coeff] : r in R @});
        for i := 1 to Ci[2] do
            Append(~Tschs, congrs);
        end for;
    end for;

    congrs := {@ &*c : c in CartesianProduct(Tschs) @};
    return {@ Reverse(Prune(Coefficients(c))) : c in congrs @};
end intrinsic;

intrinsic ComputeCongruences(L::SeqEnum, k::RngIntElt) -> SeqEnum
{Computes the collective list of defining polynomials of O_E/O_B
modulo p^k for all E in a list L}
    for E in L do
        assert InertiaDegree(BaseRing(E)) eq 1;
    end for;
    p := Prime(BaseRing(L[1]));
    for E in L do
        assert Prime(BaseRing(E)) eq p;
    end for;

    C := {@ @};
    for E in L do
        E;
        time C join:= ComputeCongruences(E,k);
    end for;
    return C;
end intrinsic;

intrinsic WriteCongruences(file::MonStgElt, C::SetIndx)
{Writes a list of congruences modulo p^k to a file}
    cha := Characteristic(Parent(C[1][1]));
    b,p,k := IsPrimePower(cha);
    assert b;
    n := #C[1];

    //compute Newton-Ore exponents (fixed divisors)
    exp := [];
    divs := [];
    for i := 1 to n do
        mink := k;
        for c in C do
            vci := Valuation(Z!c[i],p);
            if mink gt vci then
                mink := vci;
            end if;
        end for;
        Append(~exp,p^(k-mink));
        Append(~divs,p^mink);
    end for;

    R := CartesianProduct([Integers(e) : e in exp]);
    L := Sort({@ R!<(Z!c[i]) div divs[i] : i in [1..#c]> : c in C @});

    //write Newto-Ore exponents to file
    s := "{ ";
    for e in exp[1..(#exp-1)] do
        s cat:= Sprintf("%o, ", e);
    end for;
    s cat:= Sprintf("%o }", exp[#exp]);
    Write(file, s: Overwrite := true);

    //write congruences to file
    Write(file, "[");
    for l in L do
        Write(file, Sprintf("%o,", l));
    end for;
    Write(file, "]");
end intrinsic;
