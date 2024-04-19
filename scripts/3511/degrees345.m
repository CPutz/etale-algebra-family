// Load this file from the main folder
AttachSpec("spec");

printf "--- Warning ---\n";
printf "Page and theorem numbers mentioned below are currently not correct.\n";
printf "---------------\n\n";

function contains_components_isomorphic_to(E1,E2);
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
end function;

load "scripts/3511/local_covering_sets.dat";

// Combine all local covering sets for different cases at the prime 3
U3 := &cat[U3_va4, U3_va6, U3_va_7_8_10, U3_va9, U3_vb3, U3_vc6];

// Combine all local covering sets for different cases at the prime 11
U11 := &cat[U11_va8, U11_vb4];

printf "\n==================================================================\n";
printf "We perform the computations from Proposition 5.22.\n";
printf "==================================================================\n\n";

//load cubic number fields unramified outside 3 and 11 and of signature (1,1)
load "scripts/3511/fields_cubic_unramified_3_11_sig_1_1.dat";
Lcubic := [L`field : L in make_data()];

Lcubic_filter3 := [L : L in Lcubic |
	exists { E3 : E3 in U3 |
		contains_components_isomorphic_to(E3, EtaleAlgebra(L,3)) }];
Lcubic_filter3_11 := [L : L in Lcubic_filter3 |
	exists { E11 : E11 in U11 |
		contains_components_isomorphic_to(E11, EtaleAlgebra(L,11)) }];
assert #Lcubic_filter3_11 eq 0;
printf "No cubic number fields unramified outside 3 and 11 and with\n";
printf "signature (1,1) satisfies the local conditions at 3 and 11.\n\n";

//load quartic number fields unramified outside 3 and 11 and of signature (0,2)
load "scripts/3511/fields_quartic_unramified_3_11_sig_0_2.dat";
Lquartic := [L`field : L in make_data()];

Lquartic_filter3 := [L : L in Lquartic |
	exists { E3 : E3 in U3 |
		contains_components_isomorphic_to(E3, EtaleAlgebra(L,3)) }];

Lquartic_filter3_11 := [L : L in Lquartic_filter3 |
	exists { E11 : E11 in U11 |
		contains_components_isomorphic_to(E11, EtaleAlgebra(L,11)) }];

assert #Lquartic_filter3_11 eq 0;
printf "No quartic number fields unramified outside 3 and 11 and with\n";
printf "signature (0,2) satisfies the local conditions at 3 and 11.\n\n";

//load quartic number fields unramified outside 3 and 11 and of signature (1,2)
//and absolute discriminant <= 793881
load "scripts/3511/fields_quintic_unramified_3_11_sig_1_2.dat";
Lquintic := [L`field : L in make_data()];

Lquintic_filter11 := [L : L in Lquintic |
	exists { E11 : E11 in U11 |
		contains_components_isomorphic_to(E11, EtaleAlgebra(L,11)) }];

printf "No quartic number fields unramified outside 3 and 11, with\n";
printf "signature (0,2), and with absolute discriminant <= 793881\n";
printf "satisfies the local conditions at 11.\n\n";

printf "done\n";

quit;
