Z := Integers();

intrinsic Etale257Degree7(p::RngIntElt
     : D := LocalFieldDatabase(),
       Neighbourhoods := false) -> SeqEnum
{}
     S<s> := PolynomialRing(Rationals());
     R<t> := PolynomialRing(S);
     F := (27*s^2 - 2268*s*t^5 + 1890*s*t^6 - 5760*s*t^7 - 1764*t^10 +
          2940*t^11 - 6265*t^12 + 4200*t^13 - 1500*t^14) / 27;
     Fs := SwitchVariables(F);

     K := pAdicField(p, 500);
     X := pAdicNbhds(K);

     E0s := [];
     for a in [2..(p-1)] do
          F0 := SwitchVariables(Evaluate(Fs, a + p*t));
          E0 := EtaleAlgebraFamily(F0, p : D := D);
          E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
          Append(~E0s, E0);
     end for;

     F1 := SwitchVariables(Evaluate(Fs, p^5*t));
     E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
     E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];
     
     F2 := SwitchVariables(Evaluate(Fs, 1 + p^2*t));
     E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, D := D);
     E2 := [<E[1], [1 + p^2 * X!B : B in E[2]]> : E in E2];

     //F3 := ReciprocalPolynomial(p^7 * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
     //E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
     //E3 := [<E[1], [Invert(p^7 * X!B) : B in E[2]]> : E in E3];

     Es := {@ @};
     //Eis := E0s cat [E1,E2,E3];
     Eis := E0s cat [E1,E2];
     for Ei in Eis do
          for E in Ei do
               Include(~Es, E[1]);
          end for;
     end for;

     EBs := {@ @};
     if Neighbourhoods then
          for E in Es do
               Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
          end for;
          Es := EBs;
     end if;

     return SetToSequence(Es);
end intrinsic;

intrinsic FindDiscriminant(p::RngIntElt) -> .
{}
     Qp := pAdicField(p,500);
     R<t> := PolynomialRing(Qp);
     S<s> := PolynomialRing(R);
     F := (27*s^2 - 2268*s*t^5 + 1890*s*t^6 - 5760*s*t^7 - 1764*t^10 +
          2940*t^11 - 6265*t^12 + 4200*t^13 - 1500*t^14) / 27;

     discs := {@ @};

     if p eq 7 then
          Cs := [a/7^(7*k) : k in [1..3], a in [0..7^3] | a mod 7 ne 0] cat
               [a : a in [0..7^3] | a mod 7 eq 4 and a mod 49 ne 32];
     elif p eq 5 then
          Cs := [a * 5^(5*k) : k in [1..3], a in [0..5^3] | a mod 5 ne 0];
     elif p eq 3 then
          Cs := [a/3^(7*k) : k in [1..3], a in [0..3^5] | a mod 3 eq 2];
     elif p eq 2 then
          Cs := [1 - (1+8*a)*2^(2*k) : k in [2..5], a in [0..2^3]] cat [1 - (20 + 2^5*a) : a in [0..2^3]];
     else
          Cs := [];
     end if;

     for c in Cs do
          _,_,Ext := Factorization(Evaluate(F, c) : Extensions := true);

          disc := 0;
          for E in Ext do
               disc +:= Valuation(Discriminant(E`Extension, Qp));
          end for;
          Include(~discs, disc);
     end for;

     return discs;
end intrinsic;

intrinsic FindDiscriminant3() -> .
{}
     Qp := pAdicField(3,500);
     R<t> := PolynomialRing(Qp);
     
     K<a> := ext<Qp | t^2 - 21>;
     
     T<x> := PolynomialRing(K);
     S<s> := PolynomialRing(T);
     F := x^5 * (378 + 84*a + (-315 - 70*a)*x + (960 + 210*a)*x^2) - 9*s;

     discs := {@ @};
     Cs := [a/3^(7*k) : k in [1..3], a in [0..3^5] | a mod 3 eq 2];

     for c in Cs do
          _,_,Ext := Factorization(Evaluate(F, c) : Extensions := true);

          disc := 0;
          for E in Ext do
               disc +:= Valuation(Discriminant(E`Extension, K));
          end for;
          Include(~discs, disc);
     end for;

     return discs;
end intrinsic;

intrinsic FindDiscriminant2() -> .
{}
     Qp := pAdicField(2,500);
     R<t> := PolynomialRing(Qp);
     
     K := UnramifiedExtension(Qp,2);
     a := Roots(t^2 - 21, K)[1,1];
     
     T<x> := PolynomialRing(K);
     S<s> := PolynomialRing(T);
     F := x^5 * (378 + 84*a + (-315 - 70*a)*x + (960 + 210*a)*x^2) - 9*s;

     discs := {@ @};
     Cs := [1 - (1+8*a)*2^(2*k) : k in [2..5], a in [0..2^3]] cat [1 - (20 + 2^5*a) : a in [0..2^3]];

     for c in Cs do
          _,_,Ext := Factorization(Evaluate(F, c) : Extensions := true);

          disc := 0;
          for E in Ext do
               disc +:= Valuation(Discriminant(E`Extension, K));
          end for;
          Include(~discs, disc);
     end for;

     return discs;
end intrinsic;

intrinsic FindDiscriminant7() -> .
{}
     Qp := pAdicField(7,500);
     R<t> := PolynomialRing(Qp);
     
     K<a> := ext<Qp | t^2 - 21>;
     
     T<x> := PolynomialRing(K);
     S<s> := PolynomialRing(T);
     F := x^5 * (378 + 84*a + (-315 - 70*a)*x + (960 + 210*a)*x^2) - 9*s;

     discs := {@ @};
     Cs := [a/7^(7*k) : k in [1..3], a in [0..7^3] | a mod 7 ne 0] cat
               [a : a in [0..7^3] | a mod 7 eq 4 and a mod 49 ne 32];
     Cs0 := [];
     for c in Cs do
          _,_,Ext := Factorization(Evaluate(F, c) : Extensions := true);

          disc := 0;
          for E in Ext do
               disc +:= Valuation(Discriminant(E`Extension, Qp));
          end for;

          if disc eq 11 then
               Append(~Cs0,c);
          end if;
          Include(~discs, disc);
     end for;

     return discs;
end intrinsic;


intrinsic Etale257Unramified_degree7(p::RngIntElt, B::SeqEnum) -> SeqEnum
{}
     Qp := pAdicField(p,500);
     R<t> := PolynomialRing(Qp);
     K<a> := QuadraticField(21);

     for P in Decomposition(K,p) do
          P;
          Kp,phi := Completion(K,P[1]);
          T<x> := PolynomialRing(Kp);
          S<s> := PolynomialRing(T);
          b := phi(a);
          F := x^5 * (378 + 84*b + (-315 - 70*b)*x + (960 + 210*b)*x^2) - 9*s;
          
          for c in B do
               {* Degree(f[1])^^f[2] : f in (Factorization(Evaluate(F,c))) *};
          end for;
     end for;

     return [];
end intrinsic;

intrinsic Etale257_degree7(p::RngIntElt) -> .
{}
     Qp := pAdicField(p,500);
     Zp := pAdicRing(p,100);
     R<t> := PolynomialRing(Qp);
     S<s> := PolynomialRing(R);
     F := (27*s^2 - 2268*s*t^5 + 1890*s*t^6 - 5760*s*t^7 - 1764*t^10 +
          2940*t^11 - 6265*t^12 + 4200*t^13 - 1500*t^14) / 27;

     if p eq 7 then
          Cs := [a/7^(7*k) : k in [1..3], a in [0..7^3] | a mod 7 ne 0] cat
               [a : a in [0..7^3] | a mod 7 eq 4 and a mod 49 ne 32];
     elif p eq 5 then
          Cs := [a * 5^(5*k) : k in [1..3], a in [0..5^3] | a mod 5 ne 0];
     elif p eq 3 then
          Cs := [a/3^(7*k) : k in [1..3], a in [0..3^5] | a mod 3 eq 2];
     elif p eq 2 then
          Cs := [1 - (1+8*a)*2^(2*k) : k in [2..5], a in [0..2^3]] cat [1 - (20 + 2^5*a) : a in [0..2^3]];
     else
          Cs := [];
     end if;
//Cs := Cs0;
#Cs;
     Es := {@ @};

     for c in Cs do
          fac := Factorization(Evaluate(F, c));
          time Esi := [<Components(EtaleAlgebra(f[1]))[1,1], f[2]> : f in fac];
          
          /*Esinew := [];
          for i := 1 to #Esi do
               Ei := Esi[i];
               if Degree(Ei[1],Zp) eq 2 then
               //     Append(~Esinew,<UnramifiedExtension(B,1), Esi[i,2]>);
               //     BaseRing(Esinew[#Esinew][1]) eq B;
               else
                    Append(~Esinew, Ei);
               end if;
          end for;*/

          E := EtaleAlgebra(Esi);
          E;
          //time E := EtaleAlgebra(Evaluate(F,c));
          Include(~Es, E);
     end for;

     return Es;
end intrinsic;


intrinsic Etale257_degree7_7() -> .
{}
     Q7 := pAdicField(7,500);
     S<s> := PolynomialRing(Q7);
     K2<a> := ext<Q7 | s^2 - 21>;
     R<t> := PolynomialRing(K2);
     phi := t^5 * ((960 + 210*a)*t^2 - (315 + 70*a)*t + (378 + 84*a)) / 9;

     Cs := [a/7^7 : a in [0..7^2-1] | a mod 7 ne 0] cat
          [a : a in [0..7^2-1] | a mod 7 eq 4];
     
     _,_,Ext1 := Factorization(t^7 - 5 : Extensions := true);
     E1 := Ext1[1]`Extension;
     E2a := ext<K2 | t^3 - 3*a>;
     Es := {@ @};

     for c in Cs do
          fac,_,ext := Factorization(phi - c : Extensions := true);
          if #fac eq 1 then
               if not IsIsomorphic(ext[1]`Extension,E1) then
                    c;
               end if;
          else
               if #fac ne 3 then
                    c;
               end if;
               for i := 1 to 3 do
                    if Degree(fac[i,1]) ne 1 then
                         if not IsIsomorphic(ext[i]`Extension,E2a) then
                              c;
                         end if;
                    end if;
               end for;
          end if;
     end for;

     return 0;
end intrinsic;

/*
intrinsic Etale257_degree7_test(p::RngIntElt) -> .
{}
     K21<a> := QuadraticField(21);
     pl := Decomposition(K21, p)[2,1];

     Kp,phi_ex := Completion(K21, pl);
     Kp`DefaultPrecision := 200; //needed to make phi(a) have high precision
     ChangePrecision(~Kp, 200);
     //map from K21 to the completion at pl with finite precision
     phi := phi_ex * Coercion(Codomain(phi_ex), Kp);

     S<s> := PolynomialRing(Kp);
     R<t> := PolynomialRing(S);
     F := t^5 * ((960 + 210*phi(a))*t^2 - (315 + 70*phi(a))*t + (378 + 84*phi(a))) / 9;

     E1 := EtaleAlgebraFamily2(F - p^5 * s : Filter := Integers(5)!0);

     Es := {@ @};
     Eis := [E1];
     for Ei in Eis do
          for E in Ei do
               Include(~Es, E[1]);
          end for;
     end for;

     return Es;
end intrinsic;

intrinsic Etale257_degree7_test2(p::RngIntElt) -> .
{}
     K<a> := QuadraticField(21);
     pl := Decomposition(K, p)[1,1];

     S<s> := PolynomialRing(K);
     R<t> := PolynomialRing(S);
     F := t^5 * ((960 + 210*a)*t^2 - (315 + 70*a)*t + (378 + 84*a)) / 9;

     E1 := EtaleAlgebraFamily2(F - p^5 * s, pl : Filter := Integers(5)!0);

     //Qp := pAdicField(p,500);
     //_<x> := PolynomialRing(Qp);
     //K21<a> := ext<Qp | x^2 - 21>;

     //S<s> := PolynomialRing(K21);
     //R<t> := PolynomialRing(S);
     //phi := t^5 * ((960 + 210*a)*t^2 - (315 + 70*a)*t + (378 + 84*a)) / 9;

     //E1 := EtaleAlgebraFamily2(phi - p^5 * s : Filter := Integers(5)!0);

     Es := {@ @};
     Eis := [E1];
     for Ei in Eis do
          for E in Ei do
               Include(~Es, E[1]);
          end for;
     end for;

     return Es;
end intrinsic;

intrinsic Etale257_degree7_test3(p::RngIntElt) -> .
{}
     K21<a> := QuadraticField(21);
     pl := Decomposition(K21, p)[1,1];

     Kp,phi_ex := Completion(K21, pl);
     Kp`DefaultPrecision := 2000; //needed to make phi(a) have high precision
     ChangePrecision(~Kp, 2000);
     //map from K21 to the completion at pl with finite precision
     phi := phi_ex * Coercion(Codomain(phi_ex), Kp);

     S<s> := PolynomialRing(Kp);
     R<t> := PolynomialRing(S);
     F := t^5 * ((960 + 210*phi(a))*t^2 - (315 + 70*phi(a))*t + (378 + 84*phi(a))) / 9;

     E1 := EtaleAlgebraFamily2(ReciprocalPolynomial(p^7 * s * F - 1) : Filter := Integers(7)!0);

     Es := {@ @};
     Eis := [E1];
     for Ei in Eis do
          for E in Ei do
               Include(~Es, E[1]);
          end for;
     end for;

     return Es;
end intrinsic;
*/