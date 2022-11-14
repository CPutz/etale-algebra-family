Q := Rationals();
Z := Integers();

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

intrinsic QuadraticNonResidue(p::RngIntElt) -> RngIntElt
{}
	for a := 2 to p-1 do
		if LegendreSymbol(a, p) eq -1 then
			return a;
		end if;
	end for;

	return 0;
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

intrinsic FactorizationPartition(f::RngUPolElt, p::RngIntElt) -> SetMulti
{}
	Rp := PolynomialRing(pAdicField(p,500));
	fac := Factorization(Rp!f);
	return {* Degree(d[1])^^d[2] : d in fac *};
end intrinsic;

intrinsic FilterLocalY2(S::SeqEnum, f::RngUPolElt) -> SeqEnum
{}
	R<x> := PolynomialRing(Q);
	psi := 25*x^3 + 20*x^2 + 14*x + 14;
	phi := 4*x^5*psi;
	Psi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	res := [];
	for p in S do
		sigs013 :=
			{@ FactorizationPartition(phi - a * (4*x - 1), p) : a in [2..(p-1)] @} join
			{@ FactorizationPartition(psi * (x^5 - a), p)     : a in [1..(p-1)] @} join
			{@ FactorizationPartition(x * (x^7 - a), p)       : a in [1..(p-1)] @};
		sigs2 :=
			{@ FactorizationPartition(Psi^2 - a*p^2*(4*x - 1), p) : a in [1,QuadraticNonResidue(p)] @};

		s := FactorizationPartition(f, p);
		if s in sigs2 then
			if s notin sigs013 then
				Append(~res, p);
			end if;
		else
			p;
		end if;
	end for;

	return res;
end intrinsic;

intrinsic FilterLocalX(S::SeqEnum, f::RngUPolElt) -> SeqEnum
{}
	R<x> := PolynomialRing(Q);
	psi := 25*x^3 + 20*x^2 + 14*x + 14;

	res := [];
	for p in S do
		sigs1 := {@ FactorizationPartition(psi * (x^5 - a), p)     : a in [1..(p-1)] @};

		s := FactorizationPartition(f, p);
		if s in sigs1 then
			Append(~res, p);
		end if;
	end for;

	return res;
end intrinsic;

intrinsic FilterLocalNotSplit(S::SeqEnum) -> SeqEnum
{}
	R<x> := PolynomialRing(Q);
	psi := 25*x^3 + 20*x^2 + 14*x + 14;
	phi := 4*x^5*psi;

	res := [];
	for p in S do
		sigs0 := {@ FactorizationPartition(phi - a * (4*x - 1), p) : a in [2..(p-1)] @};

		if forall { s : s in sigs0 | 1 notin s } then
			Append(~res,p);
		end if;
	end for;

	return res;
end intrinsic;