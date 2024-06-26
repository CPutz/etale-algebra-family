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

procedure print_rams(v, ps, rams, indices);
	header := ["p", Sprintf("v_p(%o)", v)] cat [IntegerToString(a) : a in indices];
	lines := [[IntegerToString(ps[i]), Sprintf("v_%o(d)", ps[i])] cat
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
printf "We perform the computations for Proposition 5.7. We compute the\n";
printf "possible ramification degrees of the primes 3, 5, and 11 in\n";
printf "A_x^(a,b,c), depending on v_p(a), v_p(b) and v_p(c).\n";
printf "==================================================================\n\n";

printf "\n------------------------------------------------------------------\n";
printf "performing computations for v_p(abc) = 0 and p = 3,5,11\n";
printf "------------------------------------------------------------------\n";

rams_rest := [];
for p in [3,5,11] do
	rams := [];
	printf "p = %o:", p;

	Es := EtaleAlgebras3511CoeffRamification(p, 1, 1, 1 : Precision := 1500);
	ram := { Valuation(Discriminant(E)) : E in Es };
	Append(~rams, ram);
	printf ".\n";

	Append(~rams_rest, rams);
end for;

printf "\nResult:\n";
print_rams("abc", [3,5,11], rams_rest, [0]);

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(a) <= 10 and p = 3,5,11\n";
printf "------------------------------------------------------------------\n";

rams_0 := [];
for p in [3,5,11] do
	rams := [];
	printf "p = %o:", p;
	for a := 1 to 10 do
		if p eq 11 and a mod 5 eq 3 then
			prec := 3000;
		else
			prec := 800;
		end if;
		Es := EtaleAlgebras3511CoeffRamification(p, p^a, 1, 1 : Precision := prec);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	printf "\n";
	Append(~rams_0, rams);
end for;

printf "\nResult:\n";
print_rams("a", [3,5,11], rams_0, [1..#rams_0]);

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(b) <= 6 and p = 3,5,11\n";
printf "------------------------------------------------------------------\n\n";

rams_1 := [];
for p in [3,5,11] do
	rams := [];
	printf "p = %o:", p;
	for b := 1 to 6 do
		Es := EtaleAlgebras3511CoeffRamification(p, 1, p^b, 1);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_1, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("b", [3,5,11], rams_1, [1..#rams_1]);

printf "\n------------------------------------------------------------------\n";
printf "performing computations for 1 <= v_p(c) <= 11 and p = 3,5,11\n";
printf "------------------------------------------------------------------\n\n";

rams_oo := [];
for p in [3,5,11] do
	rams := [];
	printf "p = %o:", p;
	for c := 1 to 11 do
		Es := EtaleAlgebras3511CoeffRamification(p, 1, 1, p^c : Precision := 2500);
		ram := { Valuation(Discriminant(E)) : E in Es };
		Append(~rams, ram);
		printf ".";
	end for;
	Append(~rams_oo, rams);
	printf "\n";
end for;

printf "\nResult:\n";
print_rams("c", [3,5,11], rams_oo, [1..#rams_oo]);

printf "\ndone\n";
quit;