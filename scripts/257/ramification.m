// Load this file from the main folder
AttachSpec("spec");

function to_list(rs);
	if rs eq [-1] then
		return "?";
	end if;

	s := IntegerToString(rs[1]);
	for r in rs[2..#rs] do
		s cat:= Sprintf(",%o", r);
	end for;
	return s;
end function;

procedure print_rams(v, ps, rams);
	header := [Sprintf("v_p(%o)", v)] cat [IntegerToString(a) : a in [1..#rams[1]]];
	lines := [[Sprintf("v_%o(d)", ps[i])] cat
		[ to_list(Sort(SetToSequence(r))) : r in rams[i] ]
		: i in [1..#rams]];

	max_length := Max(Max([#s : s in header]), Max([#s : s in l, l in lines]));
	for l in [header] cat lines do
		for it in l do
			printf it;
			for i := #it + 1 to max_length + 2 do
				printf " ";
			end for;
		end for;
		printf "\n";
	end for;
end procedure;

printf "\n==================================================================\n";
printf "We perform the computations from Table 6.2.\n";
printf "==================================================================\n\n";

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(a) <= 10 and p = 2,5,7\n";
printf "------------------------------------------------------------------\n";

rams_0 := [];
for p in [2,5,7] do
	rams := [];
	printf "p = %o:", p;
	for a := 1 to 10 do
		Es := EtaleAlgebras257CoeffRamification(p, p^a, 1, 1);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	printf "\n";
	Append(~rams_0, rams);
end for;

printf "\nResult:\n";
print_rams("a", [2,5,7], rams_0);

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(b) <= 4 and p = 2,5,7\n";
printf "------------------------------------------------------------------\n";

rams_1 := [];
for p in [2,5,7] do
	rams := [];
	printf "p = %o:", p;
	for b := 1 to 4 do
		Es := EtaleAlgebras257CoeffRamification(p, 1, p^b, 1);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_1, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("b", [2,5,7], rams_1);

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(c) <= 14 and p = 2,5,7\n";
printf "------------------------------------------------------------------\n";

rams_oo := [];
for p in [2,5,7] do
	rams := [];
	printf "p = %o:", p;
	for c := 1 to 14 do
		Es := EtaleAlgebras257CoeffRamification(p, 1, 1, p^c : Precision := 1500);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_oo, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("c", [2,5,7], rams_oo);

printf "\ndone\n";
quit;