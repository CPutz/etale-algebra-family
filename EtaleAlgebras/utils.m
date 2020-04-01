intrinsic Zip(L1::SeqEnum, L2::SeqEnum) -> SeqEnum[Tup]
{Zips two sequences}
	require #L1 eq #L2: "Argument 1 and Argument 2 must have the same length";
	return [<L1[i], L2[i]> : i in [1..#L1]];
end intrinsic;

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