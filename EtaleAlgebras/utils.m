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
	return {[SequenceToMultiset(s[i]) : i in PartitionToIndices(p)] : s in Permutations(L)};
end intrinsic;

intrinsic PartitionToIndices(P::SeqEnum[RngIntElt]) -> SeqEnum
{Given a partition of n, splits the sequence [1..n]
according to this partition}
	L := [];
	c := 1;
	for p in P do
		Append(~L, [c..(c+p-1)]);
		c := c + p;
	end for;
	return L;
end intrinsic;

//Sequences
intrinsic Flatten(L::SeqEnum) -> SeqEnum
{Collapses nested sequences to a single sequence}
	while Type(L[1]) eq SeqEnum do
		L := &cat L;
	end while;
	return L;
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