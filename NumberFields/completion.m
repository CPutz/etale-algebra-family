
intrinsic Completion(K::FldNum[FldRat], p::RngIntElt
    : D := LocalFieldDatabase()
) -> EtAlg
{Returns the completion of K at p.}
	Qp := pAdicField(p,500);
	Rp := PolynomialRing(Qp);
	return EtaleAlgebra(Rp!DefiningPolynomial(K) : D := D);
end intrinsic;
