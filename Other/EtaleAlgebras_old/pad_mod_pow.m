intrinsic RepresentativesModuloPower(O::RngPad, k::RngIntElt) -> SeqEnum[RngPadElt]
{Gives a sequence of representatives for O* / (O*)^k}
	requirege k, 1;
	v := Valuation(O!k);
	p := UniformizingElement(O);
	Q := quo<O | p^(2*v + 1)>;

	reps := [O!x : x in Q | Valuation(x) eq 0];
	res := [];
	for x in reps do
		if not exists {y : y in res | IsPower(x / y, k)} then
			Append(~res, x);
		end if;
	end for;

	U:= UnitGroup(O);
	assert #(U / (k*U)) eq #res;

	return res;
end intrinsic;
