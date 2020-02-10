Z := Integers();

intrinsic PhiRepresentation(f::RngUPolElt, phi::RngUPolElt) -> SeqEnum[RngUPolElt]
{Writes f as a combination of powers of phi}
  d := Degree(f) div Degree(phi);
  L := [];
  r := f;
  for i := 0 to d do
    q, r := Quotrem(r, phi^(d-i));
    Append(~L, q);
  end for;
  return Reverse(L);
end intrinsic;

intrinsic PhiNewtonPolygon(f::RngUPolElt, phi::RngUPolElt) -> NwtnPgon
{The phi-Newton polygon of f}
  rep := PhiRepresentation(f, phi);
  return NewtonPolygon([<ci[1]-1, Valuation(Content(ci[2]))> : ci in Zip([1..#rep],rep)]);
end intrinsic;

intrinsic SquareTest(f::RngUPolElt, a::RngIntElt) -> SeqEnum
{Determines the structure of the etale algebra f^2 - a*p^(2r)*t}
  K := BaseRing(Parent(f));
  p := Prime(K);

  Rp := PolynomialRing(GF(p));
  RZ := PolynomialRing(Z);
  fac := Factorization(f);
  require forall {f : f in fac | f[2] eq 1} : "Argument 1 must be seperable over Fp";

  L := [];
  for gp in fac do
    g := gp[1];
    F := GF(p^Degree(g));
    S<y> := PolynomialRing(F);
    _, z := HasRoot(S!RZ!g);

    rep := PhiRepresentation(f^2, g);
    a2 := S!RZ!rep[3];
    facg := Factorization(Evaluate(a2, z)*y^2 - a*z);
    require forall {f : f in facg | f[2] eq 1} : "Failed to determine factorization";
    L cat:= [Degree(f[1]) * Degree(g) : f in facg];
  end for;
  return L;
end intrinsic;

intrinsic UnramifiedTest(f::RngUPolElt, g::RngUPolElt, a::RngIntElt) -> SeqEnum
{Determines the structure of the etale algebra f - a*p^(2r)*g (if it is unramified)}
  K := BaseRing(Parent(f));
  p := Prime(K);

  Rp := PolynomialRing(GF(p));
  RZ := PolynomialRing(Z);
  fac := Factorization(f);
  require forall {f : f in fac | f[2] eq 1} : "Argument 1 must be seperable over Fp";

  L := [];
  for gp in fac do
    g := gp[1];
    F := GF(p^Degree(g));
    S<y> := PolynomialRing(F);
    _, z := HasRoot(S!RZ!g);

    rep := PhiRepresentation(f^2, g);
    a2 := S!RZ!rep[3];
    facg := Factorization(Evaluate(a2, z)*y^2 - a*z);
    require forall {f : f in facg | f[2] eq 1} : "Failed to determine factorization";
    L cat:= [Degree(f[1]) * Degree(g) : f in facg];
  end for;
  return L;
end intrinsic;