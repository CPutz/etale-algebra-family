Q := Rationals();

intrinsic Etale3511Unramified(p::RngIntElt) -> SeqEnum
{}
	S<s> := PolynomialRing(Q);
	R<t> := PolynomialRing(S);
	phi := (3*t^2 + t + 1)^5 * (1 - 5*t);
	psi := -s * p^11 * t * (33 + 11*t + 3*t^2)^5 - 5^10;


	Es := {@ @};
	for a in [2..(p-1)] do
		for E in EtaleAlgebraFamily3(phi - (a + p*s), p) do
			Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
		end for;
	end for;

	for E in EtaleAlgebraFamily3(phi - p^5*s, p : Filter := Integers(5)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	for E in EtaleAlgebraFamily3(phi - (1 + p^3*s), p : Filter := Integers(3)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	for E in EtaleAlgebraFamily3(ReciprocalPolynomial(psi), p : Filter := Integers(11)!0) do
		Include(~Es, {* Degree(C[1], pAdicRing(p,500))^^C[2] : C in Components(E[1]) *});
	end for;

	return Es;
end intrinsic;