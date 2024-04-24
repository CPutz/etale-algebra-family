// Load this file from the main folder
AttachSpec("spec");

printf "--- Warning ---\n";
printf "Page and theorem numbers mentioned below are currently not correct.\n";
printf "---------------\n\n";

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

printf "==================================================================\n\n";

printf "\n------------------------------------------------------------------\n";

printf "------------------------------------------------------------------\n";

rams_0 := [];
for p in [3,5,7] do
	rams := [];
	printf "p = %o:", p;
	for a := 1 to 10 do
		Es := EtaleAlgebras357CoeffRamification(p, p^a, 1, 1 : Precision := 1000);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	printf "\n";
	Append(~rams_0, rams);
end for;

printf "\nResult:\n";
print_rams("a", [3,5,7], rams_0);

printf "\n------------------------------------------------------------------\n";

printf "------------------------------------------------------------------\n\n";

rams_1 := [];
for p in [3,5,7] do
	rams := [];
	printf "p = %o:", p;
	for b := 1 to 6 do
		Es := EtaleAlgebras357CoeffRamification(p, 1, p^b, 1);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_1, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("b", [3,5,7], rams_1);

printf "\n------------------------------------------------------------------\n";

printf "------------------------------------------------------------------\n\n";

rams_oo := [];
for p in [3,5,7] do
	rams := [];
	printf "p = %o:", p;
	for c := 1 to 9 do
		Es := EtaleAlgebras357CoeffRamification(p, 1, 1, p^c : Precision := 1500);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_oo, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("c", [3,5,7], rams_oo);

printf "\ndone\n";
quit;