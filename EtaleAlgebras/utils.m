//-Infinity if L is empty and Max(L) otherwise
function sup(L);
	if IsEmpty(L) then
		return -Infinity();
	else
		return Max(L);
	end if;
end function;

//zips two sequences
function zip(L1, L2);
	error if #L1 ne #L2, "Argument 1 and Argument 2 must have the same length";
	return [<L1[i], L2[i]> : i in [1..#L1]];
end function;

//product of L which is 1 if L is empty
function prod(L);
	if IsEmpty(L) then
		return 1;
	else
		return &*L;
	end if;
end function;