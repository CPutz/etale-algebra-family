
intrinsic RamificationStructures(n::RngIntElt, c::RngIntElt, p::RngIntElt) -> SeqEnum
{All ramification structures of degree n and Artin exponent c}
  require IsPrime(p): "Argument 3 must be prime";
  Ps := Partitions(n);
  res := {};
  for P in Ps do
    L := [];
    for e in P do
      v := Valuation(e, p);
      if v eq 0 then
        Append(~L, [<e,e-1>]);
      else
        Append(~L, [<e,d> : d in [e..(v*e+e-1)]]);
      end if;
    end for;
    res join:= {Sort(TupSeq(x)) : x in CartesianProduct(L) | &+[y[2] : y in x] eq c};
  end for;
  return res;
end intrinsic;

intrinsic NewtonOreExponents(R::SeqEnum, p::RngIntElt) -> SeqEnum
{Finds the NewtonOreExponents for a ramification structure R and prime p,
given that the ideal I is the product of all primes above p}
  require IsPrime(p): "Argument 2 must be prime";
  n := &+[y[1] : y in R];
  c := &+[y[2] : y in R];
  res := [0];
  for r in R do
    e := [1]; //constant coefficient is always once divisible by p
    for i in [1..r[1]-1] do
      v := Valuation(i, p);
      Append(~e, Ceiling(-v+(r[2]-i+1)/r[1]));
    end for;
    Append(~e, [0]);
    res := NewtonOreExponentsMultiply(res, e);
  end for;
  return Reverse(Prune(res));
end intrinsic;

intrinsic NewtonOreExponentsMultiply(r1::SeqEnum, r2::SeqEnum) -> SeqEnum
{}
  return [Min([r1[j+1] + r2[d-j+1] : j in [Max(d+1-#r2,0)..Min(#r1-1,d)]]) : d in [0..(#r1+#r2-2)]];
end intrinsic;