declare type PadNbhd[PadNbhdElt];
declare attributes PadNbhd: AmbientSpace;
declare attributes PadNbhdElt: Parent, Middle, Radius, Exponent;

intrinsic PAdicNbhds(R::RngPad) -> PAdicNbhd
{}
	X := New(PadNbhd);
	X`AmbientSpace := R;
	return X;
end intrinsic;

intrinsic AmbientSpace(X::PadNbhd) -> RngPad
{}
	return X`AmbientSpace;
end intrinsic;

intrinsic Print(X::PadNbhd)
{Print X}
	printf "The space of p-adic neighbourhoods of the form c + r * (OK)^k where K = %o", AmbientSpace(X);
end intrinsic;

intrinsic 'eq'(X1::PadNbhd, X2::PadNbhd) -> BoolElt
{}
	return AmbientSpace(X1) eq AmbientSpace(X2);
end intrinsic;

intrinsic CreatePAdicNbhd(X::PadNbhd, m::RngPadElt, r::RngPadElt, k::RngIntElt) -> PadNbhdElt
{}
	requirege k, 1;
	require Valuation(r) ge 0: "Argument 2 must be integral\n";

	N := New(PadNbhdElt);
	N`Parent := X;
	N`Middle := m;
	N`Radius := r;
	N`Exponent := k;
	return N;
end intrinsic;

intrinsic IsCoercible(X::PadNbhd, x::.) -> BoolElt, .
{Return whether x is coercible into X and the result if so}
	b, y := IsCoercible(AmbientSpace(X), x);
	if ISA(Type(x), PadNbhdElt) and AmbientSpace(Parent(x)) eq AmbientSpace(X) then
		return true, x;
	elif b then
		return true, CreatePAdicNbhd(y, UniformizingElement(Parent(y))^AbsolutePrecision(y), 1);
	end if;
	return false, "Coercion into X failed";
end intrinsic;

intrinsic Parent(N::PadNbhdElt) -> RngPad
{The parent of N}
	return N`Parent;
end intrinsic;

intrinsic Middle(N::PadNbhdElt) -> RngPadElt
{The middle point of N}
	return N`Middle;
end intrinsic;

intrinsic Radius(N::PadNbhdElt) -> RngPadElt
{The radius of N}
	return N`Radius;
end intrinsic;

intrinsic Exponent(N::PadNbhdElt) -> RngIntElt
{The exponent of N}
	return N`Exponent;
end intrinsic;

intrinsic Print(N::PadNbhdElt)
{Print N}
	if Exponent(N) eq 1 then
		printf "%o + (%o) * OK", Middle(N), Radius(N);
	else
		printf "%o + (%o) * (OK)^%o", Middle(N), Radius(N), Exponent(N);
	end if;
end intrinsic;

intrinsic Representant(N::PadNbhdElt) -> BoolElt
{Returns and element of N}
	return Middle(N) + Radius(N);
end intrinsic;