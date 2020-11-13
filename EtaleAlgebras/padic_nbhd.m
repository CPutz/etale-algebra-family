Z := Integers();

declare type PadNbhd[PadNbhdElt];
declare attributes PadNbhd: AmbientSpace;
declare attributes PadNbhdElt: Parent, Middle, Radius, Exponent, Inverted;

intrinsic pAdicNbhds(K::FldPad) -> PAdicNbhd
{The space of p-adic neighbourhoods of the form c + r * (OK)^k}
	X := New(PadNbhd);
	X`AmbientSpace := K;
	return X;
end intrinsic;

intrinsic AmbientSpace(X::PadNbhd) -> FldPad
{}
	return X`AmbientSpace;
end intrinsic;

intrinsic Print(X::PadNbhd)
{Print X}
	printf "The space of p-adic neighbourhoods of the form c + r * (OK*)^k where K = %o", AmbientSpace(X);
end intrinsic;

intrinsic 'eq'(X1::PadNbhd, X2::PadNbhd) -> BoolElt
{X1 eq X2}
	return AmbientSpace(X1) eq AmbientSpace(X2);
end intrinsic;

intrinsic CreatePAdicNbhd(X::PadNbhd, m::RngPadResElt, r::FldPadElt, k::RngIntElt) -> PadNbhdElt
{}
	K := AmbientSpace(X);
	requirege k, 1;
	require Parent(r) eq K: "Argument 3 must have the the ambient space of Argument 1 as its parent";
	require Valuation(r) ge 0: "Argument 3 must be integral";
	require IsCoercible(K, m): "Argument 2 and 3 must be coercible into Argument 1";

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
	if ISA(Type(x), PadNbhdElt) and AmbientSpace(Parent(x)) eq K then
		return true, CreatePAdicNbhd(X, Middle(x), Radius(x), Exponent(x));
	elif ISA(Type(x), FldPadElt) or ISA(Type(x), RngPadElt) then
		OKp := quo<Integers(K) | UniformizingElement(K)^Precision(K)>;
		b, y := IsCoercible(OKp, x);
		if b then
			return true, CreatePAdicNbhd(X, y, UniformizingElement(K)^AbsolutePrecision(x), 1);
		end if;
	end if;

	return false, "Coercion into X failed";
end intrinsic;

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

intrinsic Invert(N::PadNbhdElt) -> PadNbhdElt
{Invert N}
	N`Inverted := true;
	return N;
end intrinsic;

intrinsic IsInverted(N::PadNbhdElt) -> BoolElt
{Returns if N is inverted}
	return N`Inverted;
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

intrinsic 'eq'(N1::PadNbhdElt, N2::PadNbhdElt) -> BoolElt
{N1 eq N2}
	return Middle(N1) eq Middle(N2) and Radius(N1) eq Radius(N2) and Exponent(N1) eq Exponent(N2);
end intrinsic;

intrinsic Representative(N::PadNbhdElt) -> FldPadElt
{Returns a nonzero element of N}
	K := AmbientSpace(Parent(N));
	c := K!(Middle(N) + ChangePrecision(Radius(N), Precision(K)));
	if Valuation(c) ge AbsolutePrecision(c) then //c is zero
		p := Prime(K);
		c := ChangePrecision(c,1);
		c +:= p^AbsolutePrecision(Radius(N)) + ChangePrecision(Radius(N), Precision(K));
	end if;
	if IsInverted(N) then
		c := c^(-1);
	end if;
	return c;
end intrinsic;

intrinsic '+'(x::., N::PadNbhdElt) -> PadNbhdElt
{x + N}
	R := Parent(Middle(N));
	b, xR := IsCoercible(R, x);
	error if not b, "Could not coerce Argument 1 into the ring over which Argument 2 is defined";
	return CreatePAdicNbhd(Parent(N), xR + Middle(N), Radius(N), Exponent(N));
end intrinsic;

intrinsic '*'(x::., N::PadNbhdElt) -> PadNbhdElt
{x * N}
	R := Parent(Middle(N));
	b, xR := IsCoercible(R, x);
	error if not b, "Could not coerce Argument 1 into the ring over which Argument 2 is defined";
	return CreatePAdicNbhd(Parent(N), xR * Middle(N), xR * Radius(N), Exponent(N));
end intrinsic;

intrinsic ContainsElementOfValuation(N::PadNbhdElt, v::RngIntResElt) -> BoolElt
{Returns whether N contains an element of valuation v mod m where v is defined mod m}
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
		
		//TODO: not completely correct I think
		b,_ := IsPower(-(K!c) / r, k);
		return b;
	end if;
end intrinsic;