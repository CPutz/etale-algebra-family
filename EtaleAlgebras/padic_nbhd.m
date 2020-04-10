Z := Integers();

declare type PadNbhd[PadNbhdElt];
declare attributes PadNbhd: AmbientSpace;
declare attributes PadNbhdElt: Parent, Middle, Radius, Exponent;

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
	printf "The space of p-adic neighbourhoods of the form c + r * (OK)^k where K = %o", AmbientSpace(X);
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

intrinsic Print(N::PadNbhdElt)
{Print N}
	if Exponent(N) eq 1 then
		printf "%o + (%o) * OK", Middle(N), Radius(N);
	else
		printf "%o + (%o) * (OK)^%o", Middle(N), Radius(N), Exponent(N);
	end if;
end intrinsic;

intrinsic 'eq'(N1::PadNbhdElt, N2::PadNbhdElt) -> BoolElt
{N1 eq N2}
	return Middle(N1) eq Middle(N2) and Radius(N1) eq Radius(N2) and Exponent(N1) eq Exponent(N2);
end intrinsic;

intrinsic Representative(N::PadNbhdElt) -> FldPadElt
{Returns and element of N}
	return AmbientSpace(Parent(N))!(Middle(N) + Radius(N));
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

intrinsic Intersection(N1::PadNbhdElt, N2::PadNbhdElt) -> BoolElt, .
{}
	X := Parent(N1);
	OK := Integers(AmbientSpace(X));
	p := UniformizingElement(OK);

	if Middle(N1) eq Middle(N2) then
		if Valuation(Radius(N1)) lt Valuation(Radius(N2)) then
			Swap(~N1, ~N2);
		end if;
		r1 := Radius(N1);
		r2 := Radius(N2);
		k1 := Exponent(N1);
		k2 := Exponent(N2);

		d, a, b := Xgcd(k1, k2);

		if not IsPower(r1 / r2, d) then
			return true, [];
		end if;

		vr1 := Valuation(r1);
		vr2 := Valuation(r2);
		vr := Valuation(r1) - Valuation(r2);
		a *:= vr div d;
		b *:= vr div d;

		e := Ceiling(a / k2);
		a -:= e * (k2 div d);
		b +:= e * (k1 div d);

		rn := r1 / (r2 * p^vr);
		error if not exists (g) {g : g in RepresentativesModuloPower(OK, k2) | IsPower(rn * g^(k1 div d), k2 div d)},
			"failed to find power";

		m := Z!(k1 * k2 / d); //Lcm
		return true, [CreatePAdicNbhd(Parent(N1), Middle(N1), r1 * p^(-a * k1 div d) * g^(k1 div d), m)];
	elif Exponent(N1) eq 1 or Exponent(N2) eq 1 then
		if Exponent(N2) eq 1 then
			Swap(~N1, ~N2);
		end if;

		c := Middle(N1) - Middle(N2);
		r1 := Radius(N1);
		r2 := Radius(N2);
		k := Exponent(N2);

		if Valuation(c) lt Valuation(r1) then
			if Valuation(c) lt Valuation(r2) then
				return true, [];
			else
				c /:= r2;
				r := r1 / r2;
				vc := Valuation(c);
				vr := Valuation(r);
				prec := Max(0, 2*(k-1)*vc - vr);

				As := [(c + r*OK!a + O(p^(vr+prec))) : a in quo<OK | p^prec>];
				return true, [X!a : a in As | IsPower(a, k)];
			end if;
		else
			return Intersection(-c + N1, N2);
		end if;
	end if;

	return false, "not implemented";
end intrinsic;