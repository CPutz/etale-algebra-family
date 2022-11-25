/*
 * 
 */

declare type EtAlg;
declare attributes EtAlg: DefiningPolynomial, Components, BaseRing,
    FactorizationStructure, Data;

/*
 * Creation of etale algebras
 */

//collapse isomorphic factors
function etale_reduce(Es);
    Esnew := [];
    while #Es gt 0 do
        K := Es[#Es];
        Prune(~Es);
        c := K[2];
        for L in Es do
            if IsIsomorphic(K[1], L[1]) then
                c := c + L[2];
                Exclude(~Es, L);
            end if;
        end for;
        Include(~Esnew, <K[1], c>);
    end while;
    return Esnew;
end function;


intrinsic EtaleAlgebra(P::RngUPolElt
    :D := LocalFieldDatabase(),
     Data := "") -> EtAlg
{Creates an etale algebra given a polynomial over a p-adic field. An optional
database of local fields D can be used for searching. The parameter Data can be
used to store some meta data with the etale algebra.}
    require Discriminant(P) ne 0:
        "Parameter 1 does not generate an etale algebra";
    K := BaseRing(Parent(P));
    require ISA(Type(K), FldPad) or ISA(Type(K), RngPad):
        "Parameter 1 should be defined over a p-adic field or ring";

    //Es := [ <FindLocalFieldExtension(f[1]: D := D), f[2]> : f in Factorization(P) ];
    E := New(EtAlg);
    E`DefiningPolynomial := P;
    E`BaseRing := K;
    fac,_,exts := Factorization(P : Extensions := true);
    E`Components := [<e`Extension,1> : e in exts];
    //E`FactorizationStructure := Sort([<AbsoluteDegree(C[1]), C[2]> : C in Components(E)]);
    if not ISA(Type(Data), MonStgElt) or Data ne "" then
        E`Data := Data;
    end if;

    return E;
end intrinsic;

intrinsic EtaleAlgebra(L::SeqEnum[Tup]
    :Data := "") -> EtAlg
{Creates an etale algebra as a product of field extensions with multiplicities}
    require not IsEmpty(L):
        "Parameter 1 should be nonempty";

    K := BaseRing(L[1][1]);
    require ISA(Type(K), FldPad) or ISA(Type(K), RngPad):
        "Components should be defined over a p-adic field or ring";
    //require forall {Li : Li in L | BaseRing(Li[1]) eq K}:
    //    "All components in Parameter 1 must be defined over the same ring";

    E := New(EtAlg);
    E`BaseRing := K;
    E`Components := etale_reduce(L);
    //E`FactorizationStructure := Sort([<AbsoluteDegree(C[1]), C[2]> : C in Components(E)]);
    if not ISA(Type(Data), MonStgElt) or Data ne "" then
        E`Data := Data;
    end if;

    return E;
end intrinsic;

intrinsic EtaleAlgebra(K::FldNum[FldRat], p::RngIntElt
    : D := LocalFieldDatabase(),
      Precision := 500) -> EtAlg
{For a number field K over Q, returns an etale algebra K ⊗ Q_p.}
    require IsPrime(p): "p must be prime";

    Qp := pAdicField(p,Precision);
    Rp := PolynomialRing(Qp);
    return EtaleAlgebra(Rp!DefiningPolynomial(K) : D := D);
end intrinsic;

intrinsic EtaleAlgebra(L::FldNum, p::PlcNumElt
    : D := LocalFieldDatabase(),
      Precision := 500) -> EtAlg
{For a number field L over K, returns an etale algebra L ⊗ K_p.}
    K := BaseRing(L);
    require K eq NumberField(p): "p must be a place of the base field of K";

    Kp,KtoKp := Completion(K,p : Precision := Precision);
    //make Kp finite precision
    /*Kpf := ChangePrecision(Kp,Precision);
    KptoKpf := Coercion(Kp,Kpf);
    R := PolynomialRing(K);
    Rp,RtoRp := ChangeRing(R, Kpf, KtoKp * KptoKpf);*/
    R := PolynomialRing(K);
    Rp,RtoRp := ChangeRing(R, Kp, KtoKp);
    return EtaleAlgebra(RtoRp(DefiningPolynomial(L)) : D := D);
end intrinsic;

intrinsic Product(L::SeqEnum[EtAlg]) -> EtAlg
{Constructs the product of a sequence of etale algebras}
    return EtaleAlgebra(&cat [<Components(Li),1> : Li in L]);
end intrinsic;

intrinsic Print(E::EtAlg)
{Print E}
    if assigned E`DefiningPolynomial then
        printf "Etale algebra defined by %o over %o", DefiningPolynomial(E), BaseRing(E);
    else
        printf "Etale algebra defined by product of %o", MultisetToSequence({* C[1]^^C[2] : C in Components(E) *});
    end if;
    if assigned E`Data then
        printf " with meta data %o", E`Data;
    end if;
end intrinsic;


/*
 * Accessing and modifying attributes
 */

intrinsic BaseRing(E::EtAlg) -> .
{The base ring of E}
    return E`BaseRing;
end intrinsic;

intrinsic DefiningPolynomial(E::EtAlg) -> RngUPolElt
{The defining polynomial of E}
    return E`DefiningPolynomial;
end intrinsic;

intrinsic MonogenicDefiningPolynomial(E::EtAlg) -> RngUPolElt
{A defining polynomial for E that is monogenic}
    return &* [MinimalPolynomial(K[1].1 + BaseRing(K[1]).1, BaseRing(E))^K[2] : K in Components(E)];
end intrinsic;

intrinsic Components(E::EtAlg) -> SeqEnum
{E as a sequence of fields with multiplicities}
	return E`Components;
end intrinsic;

intrinsic FactorizationStructure(E:EtAlg) -> SeqEnum
{The factorization structure of E}
    return E`FactorizationStructure;
end intrinsic;

intrinsic Data(E::EtAlg) -> .
{The meta data attached to E}
    return E`Data;
end intrinsic;

intrinsic SetData(~E::EtAlg, D::.)
{Sets the meta data attached to E}
    E`Data := D;
end intrinsic;

intrinsic AddData(~E::EtAlg, D::.)
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

intrinsic ClearData(~E::EtAlg)
{Clear the mete data attached to E}
    delete E`Data;
end intrinsic;

intrinsic Rank(E::EtAlg) -> RngIntElt
{The rank of E over its base ring}
    return &+[C[2] * Degree(C[2]) : C in Components(E)];
end intrinsic;

intrinsic DiscriminantUpToSquares(E::EtAlg) -> .
{The discriminant of E over its base ring correct up to squares}
    Ds := [Discriminant(Ei[1], BaseRing(E)) : Ei in Components(E) | Ei[2] mod 2 eq 1];
    if IsEmpty(Ds) then
        return 1;
    else
        return &* Ds;
    end if;
end intrinsic;

intrinsic Discriminant(E::EtAlg) -> .
{The discriminant of E over its base ring}
    return &* [Discriminant(Ei[1], BaseRing(E))^Ei[2] : Ei in Components(E)];
end intrinsic;


/*
 * Isomorphism classes of etale algebras
 */

intrinsic IsIsomorphic(E1::EtAlg, E2::EtAlg) -> BoolElt
{Determines whether two etale algebras are isomorphic}
    return forall {Ki : Ki in Components(E1) |
        exists {Li : Li in Components(E2) |
            IsIsomorphic(Ki[1],Li[1]) and Ki[2] eq Li[2]}};
end intrinsic;
 
intrinsic FindIsomorphismClasses(L::SeqEnum[EtAlg]) -> SeqEnum[EtAlg]
{Returns a sequence of representatives of isomorphism classes of a sequence
of etale algebras L}
    Fstruc := {@ FactorizationStructure(Li) : Li in L @};
    Lsplit := [[Li : Li in L | FactorizationStructure(Li) eq r] : r in Fstruc];

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

intrinsic IsDefiningPolynomial(E::EtAlg, P::RngUPolElt) -> BoolElt
{Returns true if P generates an the etale algebra isomorphic to E}
    return IsDefiningPolynomial(E, Factorization(P));
end intrinsic;

intrinsic IsDefiningPolynomial(E::EtAlg, L::SeqEnum[Tup]) -> BoolElt
{Returns true if the etale algebra generated by a list of irreducible
polynomials L is isomorphic to E}
    Es := Components(E);
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

function factorization_partition(L);
    return {* Degree(Ki[1])^^Ki[2] : Ki in L *};
end function;

intrinsic FindIsomorphismClasses(L::SeqEnum[RngUPolElt]
    : D := LocalFieldDatabase(),
      Hint := [],
      Data := []) -> SeqEnum[EtAlg]
{Creates a list of etale algebra given a sequence of polynomials over a local field}
    require Data eq [] or #L eq #Data: "L and Data must have the same length";

    use_data := Data ne [];
    Res := [];
    if use_data then
        Fs := [<Factorization(L[i]), L[i], Data[i]> : i in [1..#L]];
    else
        Fs := [<Factorization(P), P> : P in L];
    end if;

    //split polynomials up into groups with the same factorization partition
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
                    Append(~res, EtaleAlgebra(FP[2]: D := D, Data := [FP[3]]));
                else
                    Append(~res, EtaleAlgebra(FP[2]: D := D));
                end if;
            end if;
        end for;
        Res cat:= res;
    end for;
    return Res;
end intrinsic;