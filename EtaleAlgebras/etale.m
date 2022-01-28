Z := Integers();
Q := Rationals();

//Etale algebras
declare type EtAlg;
declare attributes EtAlg: DefiningPolynomial, Components, BaseRing,
    Witness, FactorizationStructure;


EtaleReduce := function(E)
    Enew := [];
    while #E gt 0 do
        K := E[#E];
        Prune(~E);
        c := K[2];
        for L in E do
            if IsIsomorphic(K[1], L[1]) then
                c := c + L[2];
                Exclude(~E, L);
            end if;
        end for;
        Include(~Enew, <K[1], c>);
    end while;
    return Enew;
end function;


intrinsic EtaleAlgebra(P::RngUPolElt
    :D := LocalFieldDatabase(),
     W := "") -> EtAlg
{Creates an etale algebra given a polynomial over a p-adic field. An optional
database of local fields D can be used for searching. A parameter W can be
set to a witness.}
    require Discriminant(P) ne 0:
        "P does not generate an etale algebra; it has double roots";

	//TODO: require?
	K := BaseRing(P);
    OK := RingOfIntegers(K);
    R := PolynomialRing(OK);
    S := PolynomialRing(K);

    F := Factorization(R ! MakeMonicIntegral(P));
    Es := [ <FindLocalFieldExtension(a[1]: D := D), a[2]> : a in F ];
    //F, _, certs := Factorization(R ! MakeMonicIntegral(P): Extensions := true);
    //Es := [<certs[i]`Extension ,F[i][2]> : i in [1..#F]];

    E := New(EtAlg);
	E`DefiningPolynomial := P;
	E`BaseRing := OK;

	E`Components := EtaleReduce(Es);
    //E`Components := Es;
    E`FactorizationStructure := Sort([<AbsoluteDegree(C[1]), C[2]> : C in Components(E)]);
    
    if not ISA(Type(W), MonStgElt) or W ne "" then
        E`Witness := W;
    end if;

	return E;
end intrinsic;

intrinsic EtaleAlgebra(L::SeqEnum[Tup]) -> EtAlg
{Creates an etale algebra given a sequence of field extensions with multiplicities}
    //TODO: require?
    //ASSERT: non-empty list
    E := New(EtAlg);
    E`BaseRing := BaseRing(L[1][1]);
    require forall(t) {K : K in L | BaseRing(K[1]) eq BaseRing(E)}:
        "All fields in L must be defined over the same ring";
    //E`DefiningPolynomial := &* [DefiningPolynomial(K[1])^K[2] : K in L];
    E`DefiningPolynomial := &* [DefiningPolynomial(K[1])^K[2] : K in L];
   
    E`Components := EtaleReduce(L);
    E`FactorizationStructure := Sort([<AbsoluteDegree(C[1]), C[2]> : C in Components(E)]);
    return E;
end intrinsic;

intrinsic EtaleAlgebra(K::RngPad) -> EtAlg
{Creates an etale algebra from a field extension of a local field}
    E := New(EtAlg);
    E`BaseRing := BaseRing(BaseRing(K));
    E`DefiningPolynomial := DefiningPolynomial(K, BaseRing(E));
    E`Components := [<K, 1>];
    return E;
end intrinsic;

intrinsic EtaleAlgebra(K::FldPad) -> EtAlg
{Creates an etale algebra from a field extension of a local field}
    E := New(EtAlg);
    E`BaseRing := BaseRing(BaseRing(K));
    E`DefiningPolynomial := DefiningPolynomial(K, BaseRing(E));
    E`Components := [<K, 1>];
    return E;
end intrinsic;

intrinsic 'eq'(E1::EtAlg, E2::EtAlg) -> BoolElt
{E1 eq E2}
    //return E1`Components eq E2`Components;
    //return BaseRing(E1) eq BaseRing(E2) and
    //    DefiningPolynomial(E1) eq DefiningPolynomial(E2);
    return IsIsomorphic(E1, E2);
end intrinsic;

intrinsic Print(E::EtAlg)
{Print E}
    printf "Etale algebra with components %o", Components(E);
    if assigned E`Witness then
        printf " with witness %o", E`Witness;
    end if;
end intrinsic;

intrinsic BaseRing(E::EtAlg) -> FldPad
{The ring over which E is defined}
    return E`BaseRing;
end intrinsic;

intrinsic DefiningPolynomial(E::EtAlg) -> RngUPolElt
{The defining polynomial of E}
    return E`DefiningPolynomial;
end intrinsic;

intrinsic Components(E::EtAlg) -> SeqEnum
{Returns the structure of E as a sequence of fields with multiplicities}
	return E`Components;
end intrinsic;

intrinsic Witness(E::EtAlg) -> .
{Get the witness of E}
    return E`Witness;
end intrinsic;

intrinsic ChangeWitness(~E::EtAlg, W::.)
{Changes the witness of E to W}
    E`Witness := W;
end intrinsic;

intrinsic Rank(E::EtAlg) -> RngIntElt
{The rank of E over its base ring}
    return Degree(DefiningPolynomial(E));
end intrinsic;

intrinsic Product(L::SeqEnum[EtAlg]) -> EtAlg
{Constructs the product of a sequence of etale algebras}
    E := New(EtAlg);
    E`DefiningPolynomial := &* [DefiningPolynomial(Ei) : Ei in L];
    E`BaseRing := BaseRing(L[1]);
    E`Components := EtaleReduce(&cat [Components(Ei) : Ei in L]);
    return E;
end intrinsic;

intrinsic DiscriminantUptoSquares(E::EtAlg) -> RngIntElt
{The discriminant of E upto squares}
    Ds := [Discriminant(Ei[1], BaseRing(E)) : Ei in Components(E) | Ei[2] mod 2 eq 1];
    if IsEmpty(Ds) then
        return 1;
    else
        return &* Ds;
    end if;
end intrinsic;

intrinsic Discriminant(E::EtAlg) -> RngIntElt
{The discriminant of E}
    return &* [Discriminant(Ei[1], BaseRing(E))^Ei[2] : Ei in Components(E)];
end intrinsic;


intrinsic FindLocalFieldExtension(P::RngUPolElt
    :D := LocalFieldDatabase()) -> RngPad
{Given an irreducible polynomial P over a local field finds the extension
generated by this polynomial. An optional database of local fields D can be
used for searching.}
	d := Degree(P);
    if d eq 1 then
        return UnramifiedExtension(BaseRing(P),1);
    end if;

    if ISA(Type(D), MyDB) then
        Exts := AllExtensions(D, BaseRing(P), d);
    else
        Exts := AllExtensions(BaseRing(P), d);
    end if;
    for Ext in Exts do
        R := PolynomialRing(Ext);
        if HasRoot(R ! P) then
            B := BaseRing(Parent(P));
            p := UniformizingElement(B);
            //f := DefiningPolynomial(Ext, B)
            if IsCoercible(BaseRing(Ext), B) then
                f := DefiningPolynomial(Ext, BaseRing(Ext));
            else
                f := DefiningPolynomial(Ext, BaseRing(BaseRing(Ext)));
            end if;
            f := ChangeRing(f, B);

            //s := Z!Floor(Separant(PolynomialRing(Q)!f, Z!p) + 1);
            //R := quo<B | p^s>;
            //reduce coefficients modulo p^s
            //fR := PolynomialRing(B)![Z!(R!c) : c in Coefficients(f)];
            fR := f;
            _,_,Exts := Factorization(fR : Extensions := true);
            assert #Exts eq 1;
            return Exts[1]`Extension;
        end if;
    end for;
    return BaseRing(P);
end intrinsic;

intrinsic ScaleCoefficients(P::RngUPolElt, c::FldPadElt) -> RngUPolElt
{Scales the Coefficients of a polynomial weighted by degree}
    t := Name(P,1);
    return c^Degree(P) * Evaluate(P, t / c);
end intrinsic;

intrinsic ScaleCoefficients(P::RngUPolElt, c::RngPadElt) -> RngUPolElt
{Scales the Coefficients of a polynomial weighted by degree}
    t := Name(P,1);
    return c^Degree(P) * Evaluate(P, t / c);
end intrinsic;

intrinsic IsIsomorphic(E1::EtAlg, E2::EtAlg) -> BoolElt
{Determines whether two etale algebras are isomorphic}
	for Ki in Components(E1) do
        found := false;
        for Li in Components(E2) do
            if IsIsomorphic(Ki[1], Li[1]) and Ki[2] eq Li[2] then
                //Exclude(~E2, Li);
                found := true;
                break;
            end if;
        end for;
        if not found then
            return false;
        end if;
    end for;
    return true;
end intrinsic;

FactorizationStructure := function(E)
    return Sort([<Degree(Ki[1]), Ki[2]> : Ki in Components(E)]);
end function;

FactorizationStructureList := function(L)
    return Sort([<Degree(Ki[1]), Ki[2]> : Ki in L]);
end function;

intrinsic IsomorphismClassesEtale(S::SeqEnum[EtAlg]) -> SeqEnum[EtAlg]
{Returns a sequence of representatives of isomorphism classes in a sequence
of etale algebras S}
    Fs := {@ FactorizationStructure(L) : L in S @};
    Lsplit := [[L : L in S | FactorizationStructure(L) eq r] : r in Fs];
    //Fs := {@ L`FactorizationStructure : L in S @};
    //Lsplit := [[L : L in S | L`FactorizationStructure eq r] : r in Fs];

    rs := [];
    for l in Lsplit do
        ls := l;
        while not IsEmpty(ls) do
            //print "reducing list of", #ls, "etale algebra(s)";
            L0 := ls[1];
            Append(~rs, L0);
            ls := [L : L in ls | not IsIsomorphic(L0, L)];
        end while;
    end for;
    return rs;
end intrinsic;

intrinsic IsDefiningPolynomialEtale(E::EtAlg, P::RngUPolElt) -> BoolElt
{Returns whether the etale algebra E generated P}
    return IsDefiningPolynomialEtale(E, Factorization(P));
end intrinsic;

intrinsic IsDefiningPolynomialEtale(E::EtAlg, L::SeqEnum[Tup]) -> BoolElt
{Returns whether the etale algebra generated by a list of irreducible
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

intrinsic EtaleAlgebraListIsomorphism(L::SeqEnum[RngUPolElt]
    :D := LocalFieldDatabase(),
     W := []) -> SeqEnum[EtAlg]
{Creates a list of etale algebra given a sequence of polynomials over a local field}
    require W eq [] or #L eq #W: "L and W must have the same length";
    if IsEmpty(L) then
        return [];
    end if;
    Res := [];
    K := BaseRing(L[1]);
    OK := RingOfIntegers(K);
    R := PolynomialRing(OK);
    if W eq [] then
        Fs := [<Factorization(R ! MakeMonicIntegral(P): Certificates := true), P> : P in L];
    else
        Fs := [<Factorization(R ! MakeMonicIntegral(L[i])), L[i], W[i]> : i in [1..#L]];
    end if;
    Fstructures := {@ FactorizationStructureList(F[1]) : F in Fs @};
    Fss := [[F : F in Fs | FactorizationStructureList(F[1]) eq Fstruct] : Fstruct in Fstructures];

    for C in Fss do
        res := [];
        for FP in C do
            found := false;
            Ec := 0;
            for E in res do
                if IsDefiningPolynomialEtale(E, FP[1]) then
                    found := true;
                    Ec := E;
                    break;
                end if;
            end for;
            if found then //add witness
                ChangeWitness(~Ec, Append(Witness(Ec), FP[3])); 
            else
                if W eq [] then
                    Append(~res, EtaleAlgebra(FP[2]: D := D));
                else
                    Append(~res, EtaleAlgebra(FP[2]: D := D, W := [FP[3]]));
                end if;
            end if;
        end for;
        Res cat:= res;
    end for;
    return Res;
end intrinsic;