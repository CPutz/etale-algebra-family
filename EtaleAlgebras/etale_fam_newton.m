//Constants
Z  := Integers();
Zx := PolynomialRing(Z);
Q  := Rationals();
Qx := PolynomialRing(Q);

//Newton polygons where the vertices may depend on a variable
declare type FamNwtnPgon;
declare attributes FamNwtnPgon: Polynomial, BaseRing, Blank, Vertices;

intrinsic FamilyOfNewtonPolygons(S::SeqEnum[RngUPolElt]) -> FamNwtnPgon
{Creates a Blank VarNewtonPolygon from a sequence of vertices}
	require not IsEmpty(S): "First argument must be non-empty";
	N := New(FamNwtnPgon);
	N`Vertices := S;
	return N;
end intrinsic;

intrinsic FamilyOfNewtonPolygons(P::RngUPolElt) -> FamNwtnPgon
{Creates a VarNewtonPolygon from a VarPolynomial}
	R := BaseRing(Parent(P));
	require assigned R`ParameterSet:
		"Argument must be defined over a valid parameter space (use CreateParameterSpace)";
	N := New(FamNwtnPgon);
	N`Polynomial := P;
	N`BaseRing := R;
	V := [];
	for i in Support(P) do
		c := Coefficient(P, i);
		v := Valuation(c);
		<v, c>;
		if Min(v) eq Max(v) then
			Append(~V, <i, Retrieve(Min(v))>);
		else
			Error("Cannot determine Newton polygon (not implemented)");
		end if;
	end for;
	N`Vertices := V;
	return N;
end intrinsic;

intrinsic Print(N::FamNwtnPgon)
{Print N}
	if assigned N`Polynomial then
		printf "Family of Newton polygons defined by polynomial %o", N`Polynomial;
	else
		printf "Family of Newton polygons with vertices %o", N`Vertices;
	end if;
end intrinsic;

intrinsic BaseRing(N::FamNwtnPgon) -> Rng
{The BaseRing of N}
	return N`BaseRing;
end intrinsic;

intrinsic Polynomial(N::FamNwtnPgon) -> RngUPolElt
{The polynomial defining N}
	return N`Polynomial;
end intrinsic;

intrinsic AllVertices(N::FamNwtnPgon) -> SeqEnum
{The sequence of vertices of N}
	return N`Vertices;
end intrinsic;

intrinsic Evaluate(N::FamNwtnPgon, r::RngIntElt) -> NwtnPgon
{Returns the fibre at r}
	Vr := [<v[1], Evaluate(v[2], r)> : v in AllVertices(N)];
	return NewtonPolygon(Vr);
end intrinsic;

intrinsic VerticesXAt(N::FamNwtnPgon, r::RngIntElt) -> SeqEnum
{Gives the x-coordinates of the lower vertices of the fibre at r}
    return [v[1] : v in LowerVertices(Evaluate(N, r))];
end intrinsic;

intrinsic VerticesAt(N::FamNwtnPgon, r::RngIntElt) -> SeqEnum
{Gives the lower vertices of the fibre at r without evaluating r}
    Vxs := VerticesXAt(N, r);
    return [v : v in AllVertices(N), x in Vxs | v[1] eq x];
end intrinsic;

intrinsic FacesAt(N::FamNwtnPgon, r::RngIntElt) -> SeqEnum[FamNwtnPgonFace]
{Gives the faces of the fibre at r without evaluating r}
	Vs := VerticesAt(N, r);
	return [FamilyOfNewtonPolygonsFace(N, Vs[i], Vs[i+1]) : i in [1..#Vs-1]];
end intrinsic;

intrinsic Faces(N::FamNwtnPgon) -> SeqEnum[FamNwtnPgonFace]
{Gives the faces of N, provided that the Newton polygon
is already converged}
	range := PowerRange(BaseRing(N));
	require FamNewtonPolygonConverged(N, range[1]):
		"Newton polygon of Argument 1 is not converged over:", range;
	return FacesAt(N, range[1]);
end intrinsic;

intrinsic SlopesAt(N::FamNwtnPgon, r::RngIntElt) -> SeqEnum[RngUPolElt]
{Gives the slopes of the fibre at r without evaluating r}
	Fs := FacesAt(N, r);
	return [Slope(F) : F in Fs];
end intrinsic;

intrinsic Slopes(N::FamNwtnPgon) -> SeqEnum[RngUPolElt]
{Gives the slopes of N, provided that the Newton polygon
is already converged}
	return [Slope(F) : F in Faces(N)];
end intrinsic;

intrinsic SplittingsAt(N::FamNwtnPgon, r::RngIntElt) -> SeqEnum
{Gives all possible ways to split the faces of the fibre at r without
evaluating r}
	faces := FacesAt(N, r);
	splits := [];

	for F in faces do
		dx := Length(F);
		d := SplitLength(F);
		Append(~splits, [<p,d> : p in RestrictedPartitions(dx, {d*a : a in [1..Z!(dx/d)]})]);
	end for;

	return [ds : ds in CartesianProduct(splits)];
end intrinsic;

intrinsic FamNewtonPolygonConverged(N::FamNwtnPgon, r::RngIntElt) -> BoolElt
{Returns whether N has converged at r}
	range := PowerRange(BaseRing(N));
	require range[1] le r and r le range[2]:
		"Argument 2 must lie in range:", range;

	V := AllVertices(N);
	Vr := [<v[1], Evaluate(v[2],r)> : v in V];
	Xs := [v[1] : v in AllVertices(NewtonPolygon(Vr))];
	Dr := [<v[1], Coefficient(v[2],1)> : v in V];
	DXs := [v[1] : v in AllVertices(NewtonPolygon(Dr))];
	return DXs subset Xs;
end intrinsic;

intrinsic FamNewtonPolygonConverge(N::FamNwtnPgon) -> RngIntElt
{Returns the r such that N is converged}
	range := PowerRange(BaseRing(N));
	r := range[1];
	while r le range[2] do
		if FamNewtonPolygonConverged(N, r) then
			return r;
		end if;
		r +:= 1;
	end while;
	return r;
end intrinsic;


//A face of a family of Newton polygons
declare type FamNwtnPgonFace;
declare attributes FamNwtnPgonFace: NewtonPolygon, P1, P2, Precision,
	EtalePossibilities;

intrinsic FamilyOfNewtonPolygonsFace(N::FamNwtnPgon, P1::Tup, P2::Tup) -> FamNwtnPgonFace
{A face of a family of Newton polygons}
	//F := FamilyOfNewtonPolygonsFace(P1, P2);
	F := New(FamNwtnPgonFace);
	F`P1 := P1;
	F`P2 := P2;
	F`NewtonPolygon := N;
	return F;
end intrinsic;

intrinsic Print(F::FamNwtnPgonFace)
{Print F}
	printf "%o-%o", P1(F), P2(F);
end intrinsic;

intrinsic P1(F::FamNwtnPgonFace) -> Tup
{The first coordinate of F}
	return F`P1;
end intrinsic;

intrinsic P2(F::FamNwtnPgonFace) -> Tup
{The second coordinate of F}
	return F`P2;
end intrinsic;

intrinsic NewtonPolygon(F::FamNwtnPgonFace) -> FamNwtnPgon
{The Newton polygon of F}
	return F`NewtonPolygon;
end intrinsic;

intrinsic Slope(F::FamNwtnPgonFace) -> RngUPolElt
{The slope of F}
	return (Qx!P2(F)[2] - P1(F)[2]) / (Q!P2(F)[1] - P1(F)[1]);
end intrinsic;

intrinsic Length(F::FamNwtnPgonFace) -> RngIntElt
{The length of F}
	return Z!P2(F)[1] - P1(F)[1];
end intrinsic;

intrinsic SplitLength(F::FamNwtnPgonFace) -> RngIntElt
{The minimal length of parts that you could split F into}
	s := Slope(F);
	if s eq 0 then
		return 1;
	end if;
	den := LCM([Denominator(c) : c in Coefficients(s)]);
	num := Zx ! (den * s);
	if ConstantCoefficient(num) ne 0 then
		return Z ! (den / GCD(ConstantCoefficient(num), den));
	else
		return Z ! (den / GCD(Content(num), den));
	end if;
end intrinsic;

intrinsic Splittings(F::FamNwtnPgonFace) -> SeqEnum
{All possible ways to split F}
	dx := Length(F);
	d := SplitLength(F);
	return [<p,d> : p in RestrictedPartitions(dx, {d*a : a in [1..Z!(dx/d)]})];
end intrinsic;

intrinsic SetPrecision(F::FamNwtnPgonFace, p::ExtReElt)
{Set the precision variable of F to p}
	F`Precision := p;
end intrinsic;

intrinsic Precision(F::FamNwtnPgonFace) -> ExtReElt
{The precision variable of F}
	return F`Precision;
end intrinsic;

intrinsic SetEtalePossibilities(F::FamNwtnPgonFace, L::SeqEnum[EtAlg])
{Set the possible etale algebras of F to L}
	F`EtalePossibilities := L;
end intrinsic;

intrinsic AddEtalePossibilities(F::FamNwtnPgonFace, E::EtAlg)
{Adds a possible etale algebras to F}
	if not assigned F`EtalePossibilities then
		F`EtalePossibilities := [E];
	else
		Append(~F`EtalePossibilities, E);
	end if;
end intrinsic;

intrinsic EtalePossibilities(F::FamNwtnPgonFace) -> SeqEnum[EtAlg]
{The possible etale algebras of F}
	return F`EtalePossibilities;
end intrinsic;