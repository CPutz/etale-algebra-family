intrinsic PermutationWithCycleStructure(S::SeqEnum) -> GrpPermElt
{}
	S := &cat[Repeat(s[1], s[2]) : s in S];
	degree := &+S;
	G := Sym(degree);
	L := [[1..S[[1]]]] cat [[(&+S[[1..i]]+1)..&+S[[1..i+1]]] : i in [1..#S-1]];
	return G!&cat[Rotate(s,-1) : s in L];
end intrinsic;

intrinsic PermutationTriplesWithCycleStructures(S0::SeqEnum, S1::SeqEnum, Soo::SeqEnum) -> SeqEnum
{}
	[S0,S1,Soo];
	degree := &+[s[1] * s[2] : s in S0];
	require &+[s[1] * s[2] : s in S1] eq degree and &+[s[1] * s[2] : s in Soo] eq degree:
		"S0, S1 and Soo must have the same sum";
	G := Sym(degree);

	s0 := PermutationWithCycleStructure(S0);
	s1s := Class(G, PermutationWithCycleStructure(S1));
	s1s := [s1 : s1 in s1s | CycleStructure(s1^(-1) * s0^(-1)) eq Soo];
	C := Centraliser(G, s0);
	Cs1s := {@ { c * s1 * c^(-1) : c in C } : s1 in s1s @};

	Rs1s := [Representative(c) : c in Cs1s];
	Ts := [<s0, s1, s1^(-1) * s0^(-1)> : s1 in Rs1s];
	res := [t : t in Ts | IsTransitive(sub<G | t[1], t[2]>)];
	
	res;
	return res;
end intrinsic;

intrinsic PermutationTriples(d::RngIntElt, r0::RngIntElt, r1::RngIntElt, roo::RngIntElt) -> SeqEnum
{}
	Pd := [Reverse(Sort([<x, Multiplicity(p, x)> : x in SequenceToSet(p)])) : p in Partitions(d)];
	Pd0  := [p : p in Pd | forall {x : x in p | r0  mod x[1] eq 0}];
	Pd1  := [p : p in Pd | forall {x : x in p | r1  mod x[1] eq 0}];
	Pdoo := [p : p in Pd | forall {x : x in p | roo mod x[1] eq 0}];

	C := CartesianProduct([Pd0, Pd1, Pdoo]);
	return &cat[PermutationTriplesWithCycleStructures(c[1], c[2], c[3]) : c in C];
end intrinsic;

intrinsic PermutationTriplesWithGenus(d::RngIntElt, r0::RngIntElt, r1::RngIntElt, roo::RngIntElt, g::RngIntElt) -> SeqEnum
{}
	Pd := [Reverse(Sort([<x, Multiplicity(p, x)> : x in SequenceToSet(p)])) : p in Partitions(d)];
	Pd0  := [p : p in Pd | forall {x : x in p | r0  mod x[1] eq 0}];
	Pd1  := [p : p in Pd | forall {x : x in p | r1  mod x[1] eq 0}];
	Pdoo := [p : p in Pd | forall {x : x in p | roo mod x[1] eq 0}];

	C := CartesianProduct([Pd0, Pd1, Pdoo]);
	return &cat[PermutationTriplesWithCycleStructures(c[1], c[2], c[3]) : c in C | GenusFromCycleStructures(c[1],c[2],c[3]) eq g];
end intrinsic;

intrinsic PermutationTriplesWithGenus2(d::RngIntElt, r0::RngIntElt, r1::RngIntElt, roo::RngIntElt, g::RngIntElt) -> SeqEnum
{}
	Pd := [Reverse(Sort([<x, Multiplicity(p, x)> : x in SequenceToSet(p)])) : p in Partitions(d)];
	Pd0  := [p : p in Pd | forall {x : x in p | r0  mod x[1] eq 0}];
	Pd1  := [p : p in Pd | forall {x : x in p | r1  mod x[1] eq 0}];
	Pdoo := [p : p in Pd | forall {x : x in p | roo mod x[1] eq 0}];

	C := CartesianProduct([Pd0, Pd1, Pdoo]);
	return [c : c in C | GenusFromCycleStructures(c[1],c[2],c[3]) eq g];
end intrinsic;

intrinsic GenusFromCycleStructures(S0::SeqEnum, S1::SeqEnum, Soo::SeqEnum) -> RngIntElt
{}
	degree := &+[s[1] * s[2] : s in S0];
	require &+[s[1] * s[2] : s in S1] eq degree and &+[s[1] * s[2] : s in Soo] eq degree:
		"S0, S1 and Soo must have the same sum";
	return 1 - degree + &+[s[2] * (s[1] - 1) : s in S0 cat S1 cat Soo] div 2;
end intrinsic;

intrinsic GenusFromTriple(t::Tup) -> RngIntElt
{}
	return GenusFromCycleStructures(CycleStructure(t[1]), CycleStructure(t[2]), CycleStructure(t[3]));
end intrinsic;