intrinsic RadicalsSubset(I::RngMPol, J::RngMPol) -> BoolElt
{Returns Rad(I) subset Rad(J)}
	//I subset Rad(J) => Rad(I) subset Rad(J)
	return forall {i : i in Generators(I) | IsInRadical(i,J)};
end intrinsic;

intrinsic RadicalsEqual(I::RngMPol, J::RngMPol) -> BoolElt
{Returns wether I and J have the same radical}
    return RadicalsSubset(I, J) and RadicalsSubset(J, I);
end intrinsic;

/*intrinsic GenPol(p::SeqEnum) -> RngUPolElt
{Produces a monic degree n polynomial with root signature p,
where p is a partition of n}
	R := PolynomialRing(Rationals(), #p);
	S<x> := PolynomialRing(R);
	f := 1;
	for i := 1 to #p do
		f *:= (x - R.i)^p[i];
	end for;
	return f;
end intrinsic;*/

intrinsic GenPol(p::SeqEnum) -> RngUPolElt
{Produces a monic degree n polynomial with root signature p,
where p is a partition of n}
	m := &+[d[2] : d in p];
	R := PolynomialRing(Rationals(), m);
	return GenPol(p, [R.i : i in [1..m]]);
end intrinsic;

intrinsic GenPol(p::SeqEnum, c::SeqEnum) -> RngUPolElt
{Produces a monic degree n polynomial with root signature p and coefficients c,
where p is a partition of n and c is a list of ring elements of length
sum_d d I_p(d) where I_p is the indicator function of p}
	R := Parent(c[1]);
	S<x> := PolynomialRing(R);
	f := 1;
	i := 1;
	for d in p do
		g := 1;
		//Horner Scheme to produce general g of degree m
		for j := 1 to d[2] do
			g *:= x;
			g +:= c[i];
			i +:= 1;
		end for;
		f *:= g^d[1];
	end for;
	return f;
end intrinsic;

intrinsic TranslateCoeff1(f::RngUPolElt) -> RngUPolElt
{Translates a degree n polynomial f such that the coefficient
of x^(n-1) is 0}
	n := Degree(f);
	c := Coefficient(f, n-1);
	x := Name(Parent(f), 1);
	return Evaluate(f, x - c / n);
end intrinsic;

intrinsic IsAdmissibleSignature(I::RngMPol, p::SeqEnum) -> BoolElt
{Determines whether a partition p of n is admissible for an 
ideal I of degree n polynomial signature invariants}
	cs := Reverse(Coefficients(TranslateCoeff1(GenPol(p))))[3..&+p+1];
	return forall {c : c in Generators(I) | Evaluate(c, [0] cat cs) eq 0};
end intrinsic;

intrinsic AdmissibleSignatures(I::RngMPol, n::RngIntElt) -> SeqEnum
{Return a list of all integer partitions of n for which I is admissible}
	return [p : p in Partitions(n) | IsAdmissibleSignature(I, p)];
end intrinsic;

intrinsic IdealSubsetAdmissible(I::RngMPol, J::RngMPol, n::RngIntElt) -> BoolElt
{}
	return AdmissibleSignatures(J, n) subset AdmissibleSignatures(I, n);
end intrinsic;

intrinsic PartitionMultiplicities(p::SeqEnum) -> SeqEnum
{}
	return [Multiplicity(p, e) : e in [1..&+p]];
end intrinsic;

intrinsic Snm(n::RngIntElt, m::RngIntElt, p::SeqEnum) -> RngIntElt
{}
	return &+[Min(n * e, m * (e-1)) : e in p];
end intrinsic;

intrinsic Inmk(d::RngIntElt, n::RngIntElt, m::RngIntElt, k::RngIntElt) -> SeqEnum
{}
	return [p : p in Partitions(d) | Snm(n, m, p) ge k+1];
end intrinsic;