intrinsic GroebnerTest(p::SeqEnum) -> SeqEnum
{}
	m := &+[d[2] : d in p];
	n := &+[d[1]*d[2] : d in p];
	R := PolynomialRing(Rationals(), m+n, "glex");
	vs := [R.i : i in [1..m]];
	Ts := [];

	ls := [R.i : i in [m+1..m+n]];
	f := GenPol([<1,n>], ls);
	for q in Permutations(vs) do
		g := GenPol(p, q);
		I := ideal<R | Coefficients(f - g)>;
		t := Cputime();
		time E := EliminationIdeal(I, Set(ls));
		Append(~Ts, <Cputime(t), q>);
	end for;
	return Ts;
end intrinsic;

intrinsic GroebnerTest2(p::SeqEnum, q::SeqEnum) -> SeqEnum
{}
	m := &+[d[2] : d in p];
	n := &+[d[1]*d[2] : d in p];
	R := PolynomialRing(Rationals(), m+n, "glex");
	vs := [R.i : i in [1..m]];

	ls := [R.i : i in [m+1..m+n]];
	f := GenPol([<1,n>], ls);
	g := GenPol(p, [R.i : i in q]);
	Factorization(g);
	I := ideal<R | Coefficients(f - g)>;
	time E := EliminationIdeal(I, Set(ls));
	return E;
end intrinsic;

intrinsic DiscriminantTest(n::RngIntElt) -> .
{}
	R := PolynomialRing(Rationals(), n, "glex");
	S := PolynomialRing(R);
	f := S!Reverse([1] cat [R.i : i in [1..n]]);
	t := Cputime();
	d := Discriminant(f);
	return Cputime(t);
end intrinsic;

intrinsic ResultantTest(n::RngIntElt) -> .
{}
	R := PolynomialRing(Rationals(), n, "glex");
	S := PolynomialRing(R);
	f := S!Reverse([1] cat [R.i : i in [1..n]]);
	t := Cputime();
	d := Subdiscriminant(f, 0);
	return Cputime(t);
end intrinsic;

intrinsic ResultantTest22(n::RngIntElt) -> .
{}
	R := PolynomialRing(Rationals(), n, "glex");
	S := PolynomialRing(R);
	f := S!Reverse([1] cat [R.i : i in [1..n]]);
	df := Derivative(f);
	t := Cputime();
	d110 := Subdiscriminant(f, 0);
	d111 := Subresultant(f,df,1);
	d123 := Subresultant(df^2,f,3);
	return Cputime(t);
end intrinsic;

intrinsic ResultantTestI(n::RngIntElt, Is::SeqEnum) -> .
{}
	R := PolynomialRing(Rationals(), n, "glex");
	S := PolynomialRing(R);
	f := S!Reverse([1] cat [R.i : i in [1..n]]);
	df := Derivative(f);
	t := Cputime();
	for i in Is do
		d := Subresultant(df^i[2], f^i[1], i[3]);
	end for;
	return Cputime(t);
end intrinsic;
