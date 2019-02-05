
intrinsic T2Bound(n::RngIntElt, D::RngIntElt) -> FldReElt
{The bound for t2 (without the trace part) provided by Hunters theorem
for degree n and discriminant D }
	return (RealField() ! HermiteConstant(n-1) * Abs(D) / n)^(1/(n-1));
end intrinsic;

intrinsic ABound(n::RngIntElt, i::RngIntElt, D::RngIntElt:
	a1 := Floor(n/3),
	t2 := T2Bound(n, D)) -> FldReElt
{The bound for ai (i >= 2)}
	require i ge 2: "Argument 2 must be >= 2";
	return (t2 + a1^2 / n)^(i/2);
end intrinsic;