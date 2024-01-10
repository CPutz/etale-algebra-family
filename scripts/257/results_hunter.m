// Load this file from the main folder
AttachSpec("spec");

Z := Integers();

//the string length of the minimal polynomial of K
function length(K);
	return #Sprint(DefiningPolynomial(K));
end function;

function uptoiso(L);
	Ls := [];
	//make a list L2 of isomorphism classes
	for K in L do
		if not exists (i) { i : i in [1..#Ls] | IsIsomorphic(K,Ls[i][1]) } then
			Append(~Ls, [K]);
		else
			Append(~Ls[i], K);
		end if;
	end for;

	//for every isomorphism class, add the polynomial with the smallest minimal polynomial
	//to the output list
	return {@ [K : K in Kiso | length(K) eq Min([length(N) : N in Kiso])][1] : Kiso in Ls @};
end function;

function disc_to_string(d);
	s := "";
	if d lt 0 then
		s cat:= "-";
	end if;
	Fac := Factorization(Z!d);
	ct := 0;
	for fac in Fac do
		ct +:= 1;
		s cat:= IntegerToString(fac[1]);
		if fac[2] ne 1 then
			s cat:= "^";
			s cat:= IntegerToString(fac[2]);
		end if;
		if ct ne #Fac then
			s cat:= "*";
		end if;
	end for;
	return s;
end function;

load "scripts/257/results_hunter_raw.m";
load "scripts/257/covering_set.m";

printf "computing isomorphism classes of number fields\n";
Ks := [NumberField(f) : f in pols];
Ks_iso := uptoiso(Ks);

discs := {@ Discriminant(Integers(K)) : K in Ks_iso @};
primes := [2,3,5,7];
algebras := [U2,U3,U5,U7];
for d in discs do
	printf "\n---------- Number fields with discriminant %o ----------\n", disc_to_string(d);
	Ksd := [K : K in Ks_iso | Discriminant(Integers(K)) eq d];
	for K in Ksd do
		Ko := K;
		is_primitive := #Subfields(Ko) eq 1;
		obstruction := [primes[i] : i in [1..#primes] | 
				not exists { Ep : Ep in algebras[i] | IsIsomorphic(EtaleAlgebra(Ko,primes[i]),Ep) }];
		printf "%o, Primitive: %o, Obstruction: %o\n", Ko, is_primitive, obstruction;
	end for;
end for;