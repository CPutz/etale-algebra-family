/*
 * Etale algebras over a local field.
 */

declare type AlgEtpAdic;
declare attributes AlgEtpAdic:
    DefiningPolynomial,
    Components,
    ComponentsIsoStructure,
    BaseRing,
    Data;

import "utils.m" : prod;

/*
 * Creation and printing of etale algebras
 */

intrinsic EtaleAlgebra(P::RngUPolElt[FldPad] : Data := "") -> AlgEtpAdic
{Creates an etale algebra given a polynomial over a p-adic field. The parameter
Data can be used to store some meta data with the etale algebra.}
    require Discriminant(P) ne 0:
        "P does not generate an etale algebra because it is not separable";
    K := BaseRing(Parent(P));

    E := New(AlgEtpAdic);
    E`DefiningPolynomial := P;
    E`BaseRing := K;
    fac,_,exts := Factorization(P : Extensions := true);
    E`Components := [e`Extension : e in exts];
    if not ISA(Type(Data), MonStgElt) or Data ne "" then
        E`Data := Data;
    end if;

    return E;
end intrinsic;

intrinsic EtaleAlgebra(L::SeqEnum[FldPad], B::FldPad : Data := "") -> AlgEtpAdic
{Given a sequence of p-adic fields over a base field B, creates the direct product.
Additional meta data can be attached using the parameter Data.}
    require not IsEmpty(L):
        "L should be nonempty";

    E := New(AlgEtpAdic);
    E`BaseRing := B;
    E`Components := L;
    if not ISA(Type(Data), MonStgElt) or Data ne "" then
        E`Data := Data;
    end if;

    return E;
end intrinsic;

intrinsic EtaleAlgebra(K::FldNum[FldRat], p::RngIntElt
    : Precision := 50) -> AlgEtpAdic
{For a number field K over Q and a prime p, creates the p-adic completion K ⊗ Q_p.
The precision for the base field can be given (deafault 50).}
    require IsPrime(p): "p must be prime";

    Qp := pAdicField(p,Precision);
    Rp := PolynomialRing(Qp);
    return EtaleAlgebra(Rp!DefiningPolynomial(K));
end intrinsic;

intrinsic EtaleAlgebra(L::FldNum[FldNum], p::PlcNumElt
    : Precision := 50) -> AlgEtpAdic
{For a number field L over K and a finite place p of K, creates the p-adic completion L ⊗ K_p.
The precision for the base fields can be given (deafault 50).}
    K := BaseRing(L);
    require K eq NumberField(p): "p must be a place of the base field of K";

    Kp,KtoKp := Completion(K,p : Precision := Precision);
    R := PolynomialRing(K);
    Rp,RtoRp := ChangeRing(R, Kp, KtoKp);
    return EtaleAlgebra(RtoRp(DefiningPolynomial(L)));
end intrinsic;

intrinsic DirectProduct(E1::AlgEtpAdic, E2::AlgEtpAdic) -> AlgEtpAdic
{Constructs the product of two etale algebras}
    return DirectProduct([E1,E2]);
end intrinsic;

intrinsic DirectProduct(L::SeqEnum[AlgEtpAdic]) -> AlgEtpAdic
{Constructs the product of a sequence of p-adic etale algebras.}
    require not IsEmpty(L):
        "L should be nonempty";
    K := BaseRing(L[1]);

    require forall {E : E in L | BaseRing(E) eq K}:
        "All etale algebras in L must be defined over the same field";

    return EtaleAlgebra(&cat [Components(Li) : Li in L], K);
end intrinsic;

intrinsic SimplifyToProduct(E::AlgEtpAdic : D := LocalFieldDatabase()) -> AlgEtpAdic
{Returns an etale algebra isomorphic to E given as a product of p-adic field extensions.}
    require assigned(E`DefiningPolynomial) : "E must have a defining polynomial";
    P := DefiningPolynomial(E);
    Cs := [ FindLocalFieldExtension(f[1]: D := D) : f in Factorization(P) ];
    
    data := "";
    if assigned(E`Data) then
        data := E`Data;
    end if;

    return EtaleAlgebra(Cs, BaseRing(E) : Data := data);
end intrinsic;

intrinsic Print(E::AlgEtpAdic)
{Print E}
    if assigned E`DefiningPolynomial then
        printf "Etale algebra defined by %o over %o", DefiningPolynomial(E), BaseRing(E);
    else
        printf "Etale algebra defined by product of %o", Components(E);
    end if;
    if assigned E`Data then
        printf " with stable neighbourhoods %o", E`Data;
    end if;
end intrinsic;


/*
 * Accessing and modifying attributes
 */

intrinsic BaseRing(E::AlgEtpAdic) -> .
{The base ring of E}
    return E`BaseRing;
end intrinsic;

intrinsic DefiningPolynomial(E::AlgEtpAdic) -> RngUPolElt
{The defining polynomial of E}
    return E`DefiningPolynomial;
end intrinsic;

intrinsic Components(E::AlgEtpAdic) -> SeqEnum
{The components of E}
	return E`Components;
end intrinsic;

intrinsic ComponentsIsoStructure(E::AlgEtpAdic) -> SeqEnum
{The components of E with multiplicites. Isomorphic factors are collapsed}
    if not assigned(E`ComponentsIsoStructure) then
        CalculateIsoStructure(~E);
    end if;

    return E`ComponentsIsoStructure;
end intrinsic;

intrinsic Data(E::AlgEtpAdic) -> .
{The meta data attached to E}
    return E`Data;
end intrinsic;

intrinsic SetData(~E::AlgEtpAdic, D::.)
{Sets the meta data attached to E}
    E`Data := D;
end intrinsic;

intrinsic AddData(~E::AlgEtpAdic, D::.)
{Adds D to the meta data attached to E}
    if not assigned E`Data then
        E`Data := [];
    end if;
    if ISA(Type(D), SeqEnum) then
        for d in D do
            Append(~E`Data, d);
        end for;
        //E`Data cat:= D;
    else
        Append(~E`Data, D);
    end if;
end intrinsic;

intrinsic ClearData(~E::AlgEtpAdic)
{Clear the meta data attached to E}
    delete E`Data;
end intrinsic;

intrinsic Dimension(E::AlgEtpAdic) -> RngIntElt
{The dimension of E over its base ring.}
    return &+[Degree(C, BaseRing(E)) : C in Components(E)];
end intrinsic;

intrinsic Discriminant(E::AlgEtpAdic) -> .
{The product of the discriminants of the components of E.}
    B := BaseRing(E);
    return prod([B!Discriminant(C, B) : C in Components(E)]);
end intrinsic;

/*
 * Isomorphism classes of etale algebras
 */

intrinsic CalculateIsoStructure(~E::AlgEtpAdic)
{Calcluates the isomorphism structure of E, i.e. a list of components
with multiplicities, where all isomorphic components are collapsed. The list
is stored in the attribute ComponentsIsoStructure.}
    if not assigned(E`ComponentsIsoStructure) then
        CsStruc := [];
        Cs := Components(E);
        while #Cs gt 0 do
            C0 := Cs[#Cs];
            Prune(~Cs);
            m := 1; //multiplicity
            for C in Cs do
                if IsIsomorphic(C, C0) then
                    m +:= 1;
                    Exclude(~Cs, C);
                end if;
            end for;
            Include(~CsStruc, <C0, m>);
        end while;

        E`ComponentsIsoStructure := CsStruc;
    end if;
end intrinsic;


intrinsic IsIsomorphic(E1::AlgEtpAdic, E2::AlgEtpAdic) -> BoolElt
{Determines whether two etale algebras are isomorphic.}
    if Dimension(E1) ne Dimension(E2) then
        return false;
    end if;

    return forall {Ki : Ki in ComponentsIsoStructure(E1) |
        exists {Li : Li in ComponentsIsoStructure(E2) |
            IsIsomorphic(Ki[1],Li[1]) and Ki[2] eq Li[2]}};
end intrinsic;
 
function factorization_partition(L);
    return {* Degree(Ki[1])^^Ki[2] : Ki in L *};
end function;

intrinsic FindIsomorphismClasses(L::SeqEnum[AlgEtpAdic]) -> SeqEnum[AlgEtpAdic]
{Returns a sequence of representatives of isomorphism classes of a sequence
of etale algebras L.}
    //group the etale algebras with the same factorization structure
    Fstruc := {@ factorization_partition(ComponentsIsoStructure(E)) : E in L @};
    Lsplit := [[E : E in L | factorization_partition(ComponentsIsoStructure(E)) eq r] : r in Fstruc];

    rs := [];
    for l in Lsplit do
        ls := l;
        while not IsEmpty(ls) do
            L0 := ls[1];
            Append(~rs, L0);
            ls := [L : L in ls | not IsIsomorphic(L0, L)];
        end while;
    end for;
    return rs;
end intrinsic;

intrinsic IsDefiningPolynomial(E::AlgEtpAdic, P::RngUPolElt) -> BoolElt
{Returns true if P generates an the etale algebra isomorphic to E}
    return IsDefiningPolynomial(E, Factorization(P));
end intrinsic;

intrinsic IsDefiningPolynomial(E::AlgEtpAdic, L::SeqEnum[Tup]) -> BoolElt
{Returns true if the etale algebra generated by a list of irreducible
polynomials L with exponents is isomorphic to E}
    Es := ComponentsIsoStructure(E);
    for f in L do
        found := false;
        for i := 1 to #Es do
            Ei := Es[i];
            if f[2] le Ei[2] and Degree(f[1]) eq AbsoluteDegree(Ei[1]) then
                R := PolynomialRing(Ei[1]);
                if HasRoot(R!f[1]) then
                    Remove(~Es, i);
                    if f[2] lt Ei[2] then
                        Append(~Es, <Ei[1], Ei[2] - f[2]>);
                    end if;
                    found := true;
                    break;
                end if;
            end if;
        end for;
        if not found then
            return false;
        end if;
    end for;
    return IsEmpty(Es);
end intrinsic;

intrinsic FindIsomorphismClasses(L::SeqEnum[RngUPolElt]
    : Hint := [],
      Data := []) -> SeqEnum[AlgEtpAdic]
{Given a sequence of separable polynomials over a local field, creates a list
of isomorphism classes of etale algebras generated by this list. The parameter
Hint can be set to a list of etale algebras that should be tested first. The
parameter Data can be set to a list of the same length as L. The etale algebras
in the output will then contain the accumulated meta data of all polynomials
which generated an etale algebra isomorphic to it.}
    require Data eq [] or #L eq #Data: "L and Data must have the same length";

    use_data := Data ne [];
    Res := [];
    if use_data then
        Fs := [<Factorization(L[i]), L[i], Data[i]> : i in [1..#L]];
    else
        Fs := [<Factorization(P), P> : P in L];
    end if;

    //group the polynomials into groups with the same factorization structure
    Fstructures := {@ factorization_partition(F[1]) : F in Fs @};
    Fss := [[F : F in Fs | factorization_partition(F[1]) eq Fstruct] : Fstruct in Fstructures];

    for C in Fss do
        res := [];
        for FP in C do
            found := false;
            //search for etale algebra among previously found algebras
            if not found then
                for E in res do
                    if IsDefiningPolynomial(E, FP[1]) then
                        found := true;
                        Ec := E;
                        break;
                    end if;
                end for;
            end if;

            //search for etale algebra among hints
            for E in Hint do
                if IsDefiningPolynomial(E, FP[1]) then
                    found := true;
                    Ec := E;
                    Append(~res, Ec);
                    break;
                end if;
            end for;

            if found then //add meta data
                if use_data then
                    AddData(~Ec, FP[3]); 
                end if;
            else
                if use_data then
                    Append(~res, EtaleAlgebra(FP[2]: Data := [FP[3]]));
                else
                    Append(~res, EtaleAlgebra(FP[2]));
                end if;
            end if;
        end for;
        Res cat:= res;
    end for;
    return Res;
end intrinsic;