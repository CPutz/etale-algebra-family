Z := Integers();

intrinsic RandomPolynomial(n::RngIntElt, M::RngIntElt) -> RngUPolElt
{Returns a random monic polynomial of degree n with integer coefficients
between -M and M}
	return PolynomialRing(Z)!([Random(-M,M) : i in [1..n]] cat [1]);
end intrinsic;

intrinsic TestSep(n::RngIntElt, p::RngIntElt) -> BoolElt, RngUPolElt, RngUPolElt
{}
	K := pAdicField(p,500);
	R := PolynomialRing(K);
	f := RandomPolynomial(n,p^10);
	s := Z!Floor(Separant(f,p) + 1);

	fe := f + p^s * (RandomPolynomial(n,p^10) - Parent(f).1^n);

	return IsIsomorphic(EtaleAlgebra(R!f), EtaleAlgebra(R!fe)), f, fe;
end intrinsic;

intrinsic Test1(n::RngIntElt, p::RngIntElt, k::RngIntElt)
{}
	for i := 1 to k do
		b,f,fe := TestSep(n,p);
		if not b then
			printf "failed with %o and %o\n", f, fe;
		end if;
	end for;
end intrinsic;