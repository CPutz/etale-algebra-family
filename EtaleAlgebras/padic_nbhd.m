/*
 * p-adic neighbourhoods of the form c + r * (OK)^k over a local field K.
 */

declare type PadNbhd[PadNbhdElt];
declare attributes PadNbhd: AmbientSpace;
declare attributes PadNbhdElt: Parent, Middle, Radius, Exponent, Inverted;

Z := Integers();

/*
 * Creation and printing of the parent space
 */

intrinsic pAdicNbhds(K::RngPadRes) -> PAdicNbhd
{The space of p-adic neighbourhoods of the form c + r * (OK)^k}
	X := New(PadNbhd);
	X`AmbientSpace := K;
	return X;
end intrinsic;

intrinsic pAdicNbhds(K::RngPadResExt) -> PAdicNbhd
{The space of p-adic neighbourhoods of the form c + r * (OK)^k}
	X := New(PadNbhd);
	X`AmbientSpace := K;
	return X;
end intrinsic;

intrinsic AmbientSpace(X::PadNbhd) -> .
{The ambient space that the neighbourhoods of X live in}
	return X`AmbientSpace;
end intrinsic;

intrinsic Print(X::PadNbhd)
{Print X}
	printf "The space of p-adic neighbourhoods of the form c + r * (OK)^k with K = %o", AmbientSpace(X);
end intrinsic;

intrinsic 'eq'(X1::PadNbhd, X2::PadNbhd) -> BoolElt
{X1 eq X2}
	return AmbientSpace(X1) eq AmbientSpace(X2);
end intrinsic;


/*
 * Creation, coercion and printing of p-adic neighbourhoods
 */

intrinsic pAdicNbhd(X::PadNbhd, m::RngPadResElt, r::RngPadResElt, k::RngIntElt) -> PadNbhdElt
{The element m + r * (OK)^k with parent X.}
	K := AmbientSpace(X);
	requirege k, 1;
	require Valuation(r) ge 0: "Argument 3 must be integral";

	N := New(PadNbhdElt);
	N`Parent := X;
	N`Middle := m;
	N`Radius := r;
	N`Exponent := k;
	N`Inverted := false;
	return N;
end intrinsic;

intrinsic pAdicNbhd(X::PadNbhd, m::RngPadResExtElt, r::RngPadResExtElt, k::RngIntElt) -> PadNbhdElt
{The element m + r * (OK)^k with parent X.}
	K := AmbientSpace(X);
	requirege k, 1;
	require Valuation(r) ge 0: "Argument 3 must be integral";

	N := New(PadNbhdElt);
	N`Parent := X;
	N`Middle := m;
	N`Radius := r;
	N`Exponent := k;
	N`Inverted := false;
	return N;
end intrinsic;

intrinsic IsCoercible(X::PadNbhd, x::.) -> BoolElt, .
{Return whether x is coercible into X and the result if so}
	K := AmbientSpace(X);
	if ISA(Type(x), PadNbhdElt) then
		N := pAdicNbhd(X, Middle(x), Radius(x), Exponent(x));
		if IsInverted(x) then
			Invert(~N);
		end if;
		return true, N;
	elif ISA(Type(x), FldPadElt) or ISA(Type(x), RngPadElt) then
		OKp := quo<Integers(K) | UniformizingElement(K)^Precision(K)>;
		b, y := IsCoercible(OKp, x);
		if b then
			return true, pAdicNbhd(X, y, UniformizingElement(K)^AbsolutePrecision(x), 1);
		end if;
	end if;

	return false, "Coercion into X failed";
end intrinsic;

intrinsic Print(N::PadNbhdElt)
{Print N}
	s := Sprintf("%o + (%o) * OK", Middle(N), Radius(N));
	if Exponent(N) gt 1 then
		s cat:= "^" cat IntegerToString(Exponent(N));
	end if;
	if IsInverted(N) then
		s := "(" cat s cat ")^{-1}";
	end if;
	printf "%o", s;
end intrinsic;


/*
 * Accessing attributes
 */

intrinsic Parent(N::PadNbhdElt) -> PadNbhd
{The parent of N}
	return N`Parent;
end intrinsic;

intrinsic Middle(N::PadNbhdElt) -> RngPadResElt
{The middle point of N}
	return N`Middle;
end intrinsic;

intrinsic Radius(N::PadNbhdElt) -> FldPadElt
{The radius of N}
	return N`Radius;
end intrinsic;

intrinsic Exponent(N::PadNbhdElt) -> RngIntElt
{The exponent of N}
	return N`Exponent;
end intrinsic;

intrinsic IsInverted(N::PadNbhdElt) -> BoolElt
{Returns if N is inverted}
	return N`Inverted;
end intrinsic;

intrinsic 'eq'(N1::PadNbhdElt, N2::PadNbhdElt) -> BoolElt
{N1 eq N2}
	return Middle(N1) eq Middle(N2) and Radius(N1) eq Radius(N2) and Exponent(N1) eq Exponent(N2);
end intrinsic;

intrinsic Representative(N::PadNbhdElt) -> .
{Returns an element of N, not equal to its middle element.}
	K := AmbientSpace(Parent(N));
	prec := Precision(K);
	if prec eq Infinity() then
		prec := K`DefaultPrecision;
	end if;
	c := Middle(N) + Radius(N);
	/*if Valuation(c) ge AbsolutePrecision(c) then //c is zero
		p := Prime(K);
		c := ChangePrecision(c,1);
		c +:= p^AbsolutePrecision(Radius(N)) + ChangePrecision(Radius(N), prec);
	end if;*/
	if IsInverted(N) then
		c := c^(-1);
	end if;
	return c;
end intrinsic;


/*
 * Operations on p-adic neighbourhoods
 */

intrinsic '+'(x::., N::PadNbhdElt) -> PadNbhdElt
{x + N}
	R := Parent(Middle(N));
	b, xR := IsCoercible(R, x);
	error if not b, "PadNbhdElt: Could not coerce Argument 1 into the ring over which Argument 2 is defined";
	return pAdicNbhd(Parent(N), xR + Middle(N), Radius(N), Exponent(N));
end intrinsic;

intrinsic '*'(x::., N::PadNbhdElt) -> PadNbhdElt
{x * N}
	R := Parent(Middle(N));
	b, xR := IsCoercible(R, x);
	error if not b, "PadNbhdElt: Could not coerce Argument 1 into the ring over which Argument 2 is defined";
	return pAdicNbhd(Parent(N), xR * Middle(N), xR * Radius(N), Exponent(N));
end intrinsic;

intrinsic Invert(N::PadNbhdElt) -> PadNbhdElt
{N^(-1)}
	N`Inverted := true;
	return N;
end intrinsic;

intrinsic Invert(~N::PadNbhdElt)
{N^(-1)}
	N`Inverted := true;
end intrinsic;

intrinsic ContainsElementOfValuation(N::PadNbhdElt, v::RngIntResElt, min::.) -> BoolElt
{Returns whether N contains an element of valuation at least min and v mod m
(where v is defined modulo m)}
	K := AmbientSpace(Parent(N));
	R := Parent(v);
	m := Modulus(R);

	c := Middle(N);
	r := Radius(N);
	k := Exponent(N);
	vc := Valuation(c);
	vr := Valuation(r);

	if c eq 0 then
		d := GCD(k, m);
		return (Z!v - vr) mod d eq 0;
	else
		//check whether N contains an element of valuation >= min
		//TODO: check whether use of IsPower is correct
		if vc lt min and (vc ne vr or not IsPower(-(K!c) div r, k)) then
			return false;
		end if;

		if R!vc eq v then
			return true;
		end if;

		for va := 0 to Ceiling((vc - vr) / k) - 1 do
			if R!(vr + k * va) eq v then
				return true;
			end if;
		end for;

		if vc lt vr then
			return false;
		end if;
		
		//TODO: is this completely correct?
		b,_ := IsPower(-(K!c) div r, k);
		return b;
	end if;
end intrinsic;