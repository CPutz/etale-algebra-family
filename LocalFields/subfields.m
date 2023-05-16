
intrinsic Subfields(F::FldPad, m::RngIntElt) -> SeqEnum
{Return all subfields of F of degree m.}
	res := [];
	//E := BaseRing(F);
	E := AllExtensions(BaseRing(F),1)[1];

	for M in AllExtensions(E, m) do
		if exists { K : K in AllExtensions(M, Degree(F) div m) | IsIsomorphic(E[1]`Extension, IntegerRing(F))
			where _,_,E := Factorization(MinimalPolynomial(K.1, E) : Extensions := true) } then
			Append(~res, M);
		end if;
	end for;

	return res;
end intrinsic;

intrinsic Subfields(F::FldPad) -> SeqEnum
{Return all subfields of F.}
	return [ M : M in Subfields(F, m), m in Divisors(Degree(F))];
end intrinsic;
