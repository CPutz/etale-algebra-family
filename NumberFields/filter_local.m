
intrinsic SignaturesEtale(E::EtAlg) -> SetMulti
{}
	return {* Degree(C[1])^^C[2] : C in Components(E) *};
end intrinsic;

intrinsic SignaturesNumField(K::FldNum, p::RngIntElt) -> SetMulti
{}
	return {* InertiaDegree(pl[1]) : pl in Decomposition(K, p) *};
end intrinsic;

intrinsic DividePartition(P::SetMulti, n::RngIntElt) -> SetIndx
{}
	Pseq := MultisetToSequence(P);
	C := [[[b*p : b in a] : a in Partitions(n)] : p in Pseq];

	return {@ {*y : y in x, x in TupSeq(c)*} : c in CartesianProduct(C) @};
end intrinsic;

intrinsic FilterLocal4(S::SeqEnum, p::RngIntElt) -> SeqEnum
{}
	E0s,E1,E2,E3 := Etale257(p);
	sigs := {@ SignaturesEtale(E[1]) : E in E0, E0 in E0s @} join
		{@ SignaturesEtale(E[1]) : E in E1 @} join
		{@ SignaturesEtale(E[1]) : E in E2 @} join
		{@ SignaturesEtale(E[1]) : E in E3 @};
	sigs;
	prec := [SequenceToMultiset(P) : P in Partitions(4) | not IsEmpty(DividePartition(SequenceToMultiset(P),2) meet sigs) ];
	prec;

	return [K : K in S | SignaturesNumField(K,p) in prec];
end intrinsic;

intrinsic FilterLocal(S::SeqEnum, p::RngIntElt) -> SeqEnum
{}
	E0s,E1,E2,E3 := Etale257(p);
	sigs := {@ SignaturesEtale(E[1]) : E in E0, E0 in E0s @} join
		{@ SignaturesEtale(E[1]) : E in E1 @} join
		{@ SignaturesEtale(E[1]) : E in E2 @} join
		{@ SignaturesEtale(E[1]) : E in E3 @};

	return [K : K in S | SignaturesNumField(K,p) in sigs];
end intrinsic;

intrinsic NonQuadraticResidue(p::RngIntElt) -> RngIntElt
{}
	for a := 2 to p-1 do
		if LegendreSymbol(a, p) eq -1 then
			return a;
		end if;
	end for;
end intrinsic;

intrinsic FilterLocalY(S::SeqEnum, f::RngUPolElt) -> SeqEnum
{}
	res := [];
	for p in S do
		E0s,E1,E2,E3 := Etale257(p);
		sigs013 := {@ SignaturesEtale(E[1]) : E in E0, E0 in E0s @} join
			{@ SignaturesEtale(E[1]) : E in E1 @} join
			{@ SignaturesEtale(E[1]) : E in E3 @};
		sigs2 := {@ SignaturesEtale(E[1]) : E in E2 @};

		s := SignaturesEtale(EtaleAlgebra(PolynomialRing(pAdicRing(p,500))!f));
		if s in sigs2 and s notin sigs013 then
			Append(~res, p);
		end if;
	end for;

	return res;
end intrinsic;