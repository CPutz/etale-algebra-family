// Load this file from the main folder
AttachSpec("spec");

/*function contains_components_isomorphic_to(E1,E2);
	C1 := Components(E1);
	C2 := Components(E2);

	I := [];
	// For every component of E2, find an isomorphic component of E1,
	// and make sure that no components are ``used twice''
	for C in C2 do
		b := exists (i) { i : i in [1..#C1] | i notin I and IsIsomorphic(C,C1[i]) };
		if not b then
			return false;
		end if;
		Append(~I, i);
	end for;

	return true;
end function;*/

function splitting_partition(E);
	return {* Degree(C[1],BaseRing(E)) ^^ C[2] : C in ComponentsIsoStructure(E) *};
end function;

// generates all subpartitions of p
function subpartitions(p);
	C := CartesianProduct([Partitions(r) : r in p]);
	return SetToSequence({@ {* r : r in ci, ci in c *} : c in C @});
end function;


printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

load "misc/scripts/257/upperbounds.m";

E2 := [ E : E in U2 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Possible local algebra(s) at 2: %o\n", E2;
printf "Valuation of possible local discriminants at 2: %o\n",
	{ Valuation(Discriminant(E)) : E in E2 };

E5 := [ E : E in U5 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 5: %o\n",
	{ Valuation(Discriminant(E)) : E in E5 };

E7 := [ E : E in U7 |
	splitting_partition(E) in subpartitions([7,1]) ];

printf "Valuation of possible local discriminants at 7: %o\n",
	{ Valuation(Discriminant(E)) : E in E7 };

