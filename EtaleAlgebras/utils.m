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

intrinsic SwitchVariables(f::RngUPolElt) -> RngUPolElt
{For a polynomial f in K[x][y] switches x and y}
	require ISA(Type(BaseRing(Parent(f))), RngUPol): "Argument 1 must be defined over R[x][y] for some ring R";
	S := Parent(f);
	R := BaseRing(S);
	T := PolynomialRing(BaseRing(R), 2);
	phi1 := hom<R -> T | T.1>;
	phi2 := hom<S -> T | phi1, T.2>;
	phi3 := hom<T -> S | S.1, R.1>;
	return phi3(phi2(f));
end intrinsic;