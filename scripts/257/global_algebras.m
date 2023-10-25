// Load this file from the main folder
AttachSpec("spec");

Z := Integers();

function uptoiso(L);
	Ls := {@ @};
	for K in L do
		if not exists { K2 : K2 in Ls | IsIsomorphic(K,K2) } then
			Include(~Ls, K);
		end if;
	end for;
	return Ls;
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

load "scripts/257/results_hunter.m";
load "scripts/257/upperbounds.m";

printf "computing number fields\n";
Ks := [NumberField(f) : f in pols];
Ks_iso := uptoiso(Ks);

discs := {@ Discriminant(Integers(K)) : K in Ks_iso @};
primes := [2,3,5,7];
algebras := [U2,U3,U5,U7];
for d in discs do
	printf "---------- Number fields with discriminant %o ----------\n", disc_to_string(d);
	Ksd := [K : K in Ks_iso | Discriminant(Integers(K)) eq d];
	for K in Ksd do
		Ko := OptimizedRepresentation(K);
		is_primitive := #Subfields(Ko) eq 1;
		obstruction := [primes[i] : i in [1..#primes] | 
				not exists { Ep : Ep in algebras[i] | IsIsomorphic(EtaleAlgebra(Ko,primes[i]),Ep) }];
		printf "%o, Primitive: %o, Obstruction: %o\n", Ko, is_primitive, obstruction;
	end for;
	printf "\n";
end for;