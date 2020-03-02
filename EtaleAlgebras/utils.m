intrinsic Zip(L1::SeqEnum, L2::SeqEnum) -> SeqEnum[Tup]
{Zips two sequences}
	require #L1 eq #L2: "Argument 1 and Argument 2 must have the same length";
	return [<L1[i], L2[i]> : i in [1..#L1]];
end intrinsic;