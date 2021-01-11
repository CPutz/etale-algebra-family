Z := Integers();
primes := [2,5,7];
func := Etale257Linear;
data := LocalFieldDatabaseOctic2Adics();
//root := "/home/cp/Git/congruences/input/";
root := "/home/cp/PhD/257_degree7/input/";

l_discs := [];
exps := [];

for p in primes do
	Zp := pAdicRing(p, 500);
	E0, E1, E2, E3 := func(p : D := data);

	Es := {E[1] : E in E0i, E0i in E0} join {E[1] : E in E1} join {E[1] : E in E2} join {E[1] : E in E3};

	vs := SetToSequence({Z!Valuation(Discriminant(E)) : E in Es});
	Append(~l_discs, vs);

	R<x> := PolynomialRing(Rationals());
	root_p := root cat IntegerToString(p) cat "/e";
	vE := AssociativeArray();
	for v in vs do
		vE[v] := [];
	end for;

	for E in Es do
		v := Z!Valuation(Discriminant(E));
		E;
	    Append(~vE[v], NewtonOreExponents(E, p));
	end for;

	min_v := AssociativeArray();
	for v in vs do
		min_v[v] := [Min([x[i] : x in vE[v]]) : i in [1..#vE[v][1]]];

		s := Sprintf("Divisors={%o", p^min_v[v][1]);
		for x in [p^x : x in min_v[v][2..#min_v[v]]] do
			s cat:= Sprintf(", %o", x);
		end for;
		s cat:= "}";
		Write(root_p cat IntegerToString(v) cat ".txt", s : Overwrite := true);
	end for;
	Append(~exps, min_v);

	//save defining polynomials
	for E in Es do
		v := Z!Valuation(Discriminant(E));
		pol := MultisetToSequence({*R!DefiningPolynomial(C[1], Zp)^^C[2] : C in Components(E)*});
		s := Sprintf("Pol={%o", pol[1]);
		for f in pol[2..#pol] do
			s cat:= Sprintf(", %o", f);
		end for;
		s cat:= "}";
	    Write(root_p cat IntegerToString(v) cat ".txt", s);
	end for;

end for;

for vs in CartesianProduct(l_discs) do
	file_name := root cat Sprintf("info%o%o%o.txt", vs[1], vs[2], vs[3]);
	Write(file_name, Sprintf("Disc=%o", primes[1]^vs[1] * primes[2]^vs[2] * primes[3]^vs[3]): Overwrite := true);
	divisors := [1 : i in [1..#exps[1][vs[1]]]];
	for i := 1 to 3 do
		p := primes[i];
		exp := exps[i][vs[i]];
		divisors := [divisors[j] * p^exp[j] : j in [1..#divisors]];
	end for;
	Write(file_name, Sprintf("Divisors=%o", divisors));
end for;

exit;
