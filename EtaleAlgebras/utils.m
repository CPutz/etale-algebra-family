//Permutations and partitions
intrinsic Permutations(L::SeqEnum) -> SeqEnum
{All permutations of L}
	S := Set([1..#L]);
	return [L[p] : p in Permutations(S)];
end intrinsic;

intrinsic Partitions(M::SetMulti, p::SeqEnum[RngIntElt]) -> SeqEnum
{All partitions of M in k parts}
	require #M eq (&+ p): "Argument 2 must be a partition of #Argument 1 elements";
	L := MultisetToSequence(M);
	return {[SequenceToMultiset(s[i]) : i in Partition([1..#M], p)] : s in Permutations(L)};
end intrinsic;

//Sequences
intrinsic Flatten(L::SeqEnum) -> SeqEnum
{Collapses nested sequences to a single sequence}
	while Type(L[1]) eq SeqEnum do
		L := &cat L;
	end while;
	return L;
end intrinsic;

intrinsic Zip(L1::SeqEnum, L2::SeqEnum) -> SeqEnum[Tup]
{Zips two sequences}
	require #L1 eq #L2: "Argument 1 and Argument 2 must have the same length";
	return [<L1[i], L2[i]> : i in [1..#L1]];
end intrinsic;

//Misc
intrinsic TupSeq(t::Tup) -> SeqEnum
{The tuple t as a sequence}
	return [c : c in t];	
end intrinsic;

intrinsic Swap(~x::., ~y::.)
{Swaps the values of x and y}
	temp := x;
	x := y;
	y := temp;
end intrinsic;

intrinsic Sign(f::RngUPolElt[FldRat]) -> RngIntElt
{Sign of the leading coefficient of the univariate integer polynomial f}
	if f eq 0 then
		return 0;
	else
		return Sign(LeadingCoefficient(f));
	end if;
end intrinsic;

intrinsic Evaluate(Q::SeqEnum[RngUPolElt], x::RngElt) -> SeqEnum[RngElt]
{Evaluates every polynomial in a sequence at x}
	return [Evaluate(p, x) : p in Q];
end intrinsic;

intrinsic Evaluate(Q::SeqEnum[RngMPolElt], x::SeqEnum[RngElt]) -> SeqEnum[RngElt]
{Evaluates every polynomial in a sequence at x}
	return [Evaluate(p, x) : p in Q];
end intrinsic;