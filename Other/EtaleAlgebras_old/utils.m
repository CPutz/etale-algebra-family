intrinsic Zip(L1::SeqEnum, L2::SeqEnum) -> SeqEnum[Tup]
{Zips two sequences}
	require #L1 eq #L2: "Argument 1 and Argument 2 must have the same length";
	return [<L1[i], L2[i]> : i in [1..#L1]];
end intrinsic;

intrinsic TupSeq(t::Tup) -> SeqEnum
{The tuple t as a sequence}
	return [c : c in t];	
end intrinsic;

intrinsic SeqTup(S::SeqEnum) -> Tup
{The sequence t as a tuple}
	t := <>;
	for e in S do
		Append(~t, e);
	end for;
	return t;
end intrinsic;

intrinsic Swap(~x::., ~y::.)
{Swaps the values of x and y}
	temp := x;
	x := y;
	y := temp;
end intrinsic;

intrinsic Repeat(x::., k::RngIntElt) -> SeqEnum
{Returns the list of x repeated k times}
	return [x : i in [1..k]];
end intrinsic;

intrinsic Sup(L::SeqEnum) -> .
{-Infinty() if L is empty and Max(L) otherwise}
	if IsEmpty(L) then
		return -Infinity();
	else
		return Max(L);
	end if;
end intrinsic;

intrinsic UptoIsomorphism(S::SeqEnum) -> SeqEnum
{Given a sequence of objects S for which IsIsomorphic is defined,
returns a subsequence of S which contains a representative from
each isomorphism class.}
	res := [];
	for s in S do
		if forall {t : t in res | not IsIsomorphic(s,t)} then
			Append(~res, s);
		end if;
	end for;
	return res;
end intrinsic;