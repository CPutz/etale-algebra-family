Z := Integers();

intrinsic T2Bound(n::RngIntElt, D::RngIntElt) -> FldReElt
{The bound for t2 (without the trace part) provided by Hunters theorem
for degree n and discriminant D }
	return (RealField() ! HermiteConstant(n-1) * Abs(D) / n)^(1/(n-1));
end intrinsic;

intrinsic SBound(n::RngIntElt, i::RngIntElt, D::RngIntElt:
	a1 := Floor(n/2),
	t2 := T2Bound(n, D)) -> FldReElt
{The bound for si (i >= 2)}
	require i ge 2: "Argument 2 must be >= 2";
	return (t2 + a1^2 / n)^(i/2);
end intrinsic;

intrinsic HunterIdeal(K::FldNum, I::RngOrdIdl) -> SeqEnum
{}
	OK := Integers(K);
	n := Degree(K);
	D := Discriminant(K);
	m := Index(OK, I);
	l := MinimalInteger(I);
	t2 := (RealField() ! HermiteConstant(n-1) * m^2 * Abs(D) / (n * l^2))^(1/(n-1));

	B := [K!b : b in Basis(I)];
	C := CartesianPower([-20..20], Degree(K));
	T := [&+[b[1]*b[2] : b in Zip(TupSeq(c), B)] : c in C];
	
	return [<t, Trace(t)> : t in T | Length(t) le 2*Trace(t)^2/n + t2 and
		0 le Trace(t) and Trace(t) le l*n/2 and t in I];
end intrinsic;

intrinsic HunterTrace0(K::FldNum) -> SeqEnum
{}
	n := Degree(K);
	D := Discriminant(K);
	t2 := 	T2Bound(n, D);

	B := IntegralBasis(K);
	C := CartesianPower([-20..20], Degree(K));
	T := [&+[b[1]*b[2] : b in Zip(TupSeq(c), B)] : c in C];

	return [t : t in T | Length(t) le n^3 + t2 and Trace(t) eq 0];
end intrinsic;