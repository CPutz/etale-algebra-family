/*
 * p-adic neighbourhoods of the form c + r * (OK)^k over a local field K.
 */

declare type PadNbhd[PadNbhdElt];
declare attributes PadNbhd: AmbientSpace, Prime, MinVal, CongrVal, Uniformizer;
declare attributes PadNbhdElt: Parent, Middle, Radius, Exponent, Inverted;

import "utils.m" : prod;

Z := Integers();

/*
 * Creation and printing of the parent space
 */

intrinsic pAdicNbhdSpace(K::FldRat, p::RngIntElt :
	MinVal := 0, CongrVal := Integers(1)!0) -> PAdicNbhd
{The space of p-adic neighbourhoods of the form c + r * (ZZ_p)^k
with possible additional constraints of the form v(x) >= m and
v(x) = a (mod b)}
	X := New(PadNbhd);
	X`AmbientSpace := K;
	X`Prime := p;
	X`MinVal := MinVal;
	X`CongrVal := CongrVal;
	X`Uniformizer := p;
	return X;
end intrinsic;

intrinsic pAdicNbhdSpace(K::FldNum, p::PlcNumElt :
	MinVal := 0, CongrVal := Integers(1)!0) -> PAdicNbhd
{The space of p-adic neighbourhoods of the form c + r * (OK_p)^k
with possible additional constraints of the form v(x) >= m and
v(x) = a (mod b)}
	X := New(PadNbhd);
	X`AmbientSpace := K;
	X`Prime := p;
	X`MinVal := MinVal;
	X`CongrVal := CongrVal;
	X`Uniformizer := UniformizingElement(p);
	return X;
end intrinsic;

intrinsic AmbientSpace(X::PadNbhd) -> .
{The ambient space that the neighbourhoods of X live in}
	return X`AmbientSpace;
end intrinsic;

intrinsic Prime(X::PadNbhd) -> .
{The prime element of the ambient space of X at which we take
the completion}
	return X`Prime;
end intrinsic;

intrinsic MinValuation(X::PadNbhd) -> RngIntElt
{The minimal valuation of the elements belonging to the
nbhds of X}
	return X`MinVal;
end intrinsic;

intrinsic CongrValuation(X::PadNbhd) -> RngIntResElt
{This returns a class a of ZZ/bZZ such that if N in X, then
v(x) = a (mod b) for all x in N}
	return X`CongrVal;
end intrinsic;

intrinsic UniformizingElement(X::PadNbhd) -> .
{A uniformizer of the completion of the ambient space of X at p}
	return X`Uniformizer;
end intrinsic;

intrinsic Print(X::PadNbhd)
{Print X}
	printf "The space of p-adic neighbourhoods of the form c + r * (O_K)^k intersected with {x in O_K | v(x) >= %o and v(x) = %o (mod %o)}, and K = %o",
		MinValuation(X), Z!CongrValuation(X), Modulus(Parent(CongrValuation(X))), Completion(AmbientSpace(X),Prime(X));
end intrinsic;

intrinsic 'eq'(X1::PadNbhd, X2::PadNbhd) -> BoolElt
{X1 eq X2}
	return AmbientSpace(X1) eq AmbientSpace(X2) and Prime(X1) eq Prime(X2) and
		MinValuation(X1) eq MinValuation(X2) and CongrValuation(X1) eq CongrValuation(X2);
end intrinsic;


/*
 * Creation, coercion and printing of p-adic neighbourhoods
 */

intrinsic pAdicNbhd(X::PadNbhd, m::., r::., k::RngIntElt) -> PadNbhdElt
{The element m + r * (OK)^k with parent X.}
	K := AmbientSpace(X);
	require Type(K) eq FldRat: "Base field of X must be the rationals";
	require IsCoercible(K,m): "Argument 2 must be coercible to the rationals";
	require IsCoercible(K,r): "Argument 3 must be coercible to the rationals";
	requirege k, 1;
	require Valuation(r, Prime(X)) ge 0: "Argument 3 must be integral";

	N := New(PadNbhdElt);
	N`Parent := X;
	N`Middle := m;
	N`Radius := r;
	N`Exponent := k;
	N`Inverted := false;
	return N;
end intrinsic;

intrinsic pAdicNbhd(X::PadNbhd, m::FldNumElt, r::FldNumElt, k::RngIntElt) -> PadNbhdElt
{The element m + r * (OK)^k with parent X.}
	K := AmbientSpace(X);
	require K eq Parent(m): "Argument 2 must be an element of the ambient space of X";
	require K eq Parent(r): "Argument 3 must be an element of the ambient space of X";
	requirege k, 1;
	require Valuation(r, Prime(X)) ge 0: "Argument 3 must be integral";

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
		if X eq Parent(x) then
			N := pAdicNbhd(X, Middle(x), Radius(x), Exponent(x));
			if IsInverted(x) then
				Invert(~N);
			end if;
			return true, N;
		end if;
	/*elif ISA(Type(x), FldPadElt) or ISA(Type(x), RngPadElt) then
		b, y := IsCoercible(K, x);
		if b then
			p := 
			return true, pAdicNbhd(X, y, UniformizingElement(K)^AbsolutePrecision(x), 1);
		end if;
	end if;*/
	end if;

	return false, "Coercion into X failed";
end intrinsic;

intrinsic Print(N::PadNbhdElt)
{Print N}
	s := Sprintf("%o + %o * ", Middle(N), Radius(N));
	if Exponent(N) gt 1 then
		s cat:= "(OK^" cat IntegerToString(Exponent(N)) cat " - {0})";
	else
		s cat:= "OK";
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
	return Parent(N1) eq Parent(N2) and Middle(N1) eq Middle(N2) and
		Radius(N1) eq Radius(N2) and Exponent(N1) eq Exponent(N2);
end intrinsic;

intrinsic Representative(N::PadNbhdElt) -> .
{Returns an element of N, not equal to its middle element}
	c := Middle(N) + Radius(N);
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

intrinsic IsEmpty(N::PadNbhdElt) -> BoolElt
{Return whether N is empty, considering the conditions on the minimal
valuation and congruence on the valuation imposed by the parent of N}
	X := Parent(N);
	p := Prime(X);
	K,phi := Completion(AmbientSpace(X),p);
	min := MinValuation(X);
	v := CongrValuation(X);
	R := Parent(v);
	m := Modulus(R);

	c := Middle(N);
	r := Radius(N);
	k := Exponent(N);
	vc := Valuation(c,p);
	vr := Valuation(r,p);

	d := GCD(k, m);

	if c eq 0 then
		return (Z!v - vr) mod d ne 0;
	else
		//compute largest n such that v(r) + nk < v(c)
		nl := Ceiling((vc - vr) / k - 1);

		//compute smallest n such that v(r) + nk >= min
		ns := Ceiling((min - vr) / k);

		//check whether there exists ns <= n <= nl with v(r) + nk = v (mod m)
		if (Z!v - vr) mod d eq 0 then
			//formulate reduced problem n * k2 = v2 mod m2
			k2 := k div d;
			v2 := (v - vr) div d;
			m2 := m div d;
			//solution
			s := Z!(Inverse(Integers(m2)!k2) * v2);

			//check whether there exists a global solution ns <= n <= nl:
			s_min := ns + ((s - ns) mod m);
			if s_min le nl then
				return false;
			end if;
		end if;

		//check whether a solution exists of valuation v(c)
		if vc ge min then
			if vc - v eq 0 then
				return false;
			end if;
		end if;

		//case where all elements of N have valuation equal to v(c)
		if vc lt vr then
			return true;
		end if;

		//check whether any solutions c + r*x^k may exist for which v(c) = v(r * x^k)
		if (vc - vr) mod k ne 0 then
			return true;
		end if;

		error "not implemented";

		//a solution only exists if c + r x^k = 0 mod p^min has a solution
		/*if not IsPower(-c div r, k) then
			return true;
		end if;*/

		error "not implemented";
	end if;
end intrinsic;

intrinsic 'subset'(N1::PadNbhdElt, N2::PadNbhdElt) -> BoolElt
{N1 subset N2}
	require Parent(N1) eq Parent(N2): "N1 and N2 must have the same Parent";
	if (IsInverted(N1) and not IsInverted(N2)) or
		not IsInverted(N1) and IsInverted(N2) then
		return false;
	end if;

	X := Parent(N1);
	K := AmbientSpace(X);
	p := Prime(X);

	c1 := Middle(N1);
	r1 := Radius(N1);
	k1 := Exponent(N1);
	vc1 := Valuation(c1,p);
	vr1 := Valuation(r1,p);

	c2 := Middle(N2);
	r2 := Radius(N2);
	k2 := Exponent(N2);
	vc2 := Valuation(c2,p);
	vr2 := Valuation(r2,p);

	if Valuation(c1 - c2,p) lt Valuation(r2,p) then
		return false;
	elif Valuation(r1) lt Valuation(r2,p) then
		return false;
	end if;

	c := (c1 - c2) div r2;
	r := r1 div r2;
	vc := Valuation(c,p);
	vr := Valuation(r,p);

	//TODO: this works for primes in number fields?
	if p eq 2 then
		l1 := 2^Valuation(k1,2);
		l2 := 2^Valuation(k2,2);
	else
		l1 := prod([q[1]^q[2] : q in Factorization(k1) | (p-1) mod q[1] eq 0]);
		l2 := prod([q[1]^q[2] : q in Factorization(k2) | (p-1) mod q[1] eq 0]);
	end if;

	if c eq 0 then
		if vr lt 0 then
			return false;
		end if;

		if not IsPower(r,l2) then
			return false;
		end if;

		if l1 mod l2 ne 0 then
			return false;
		end if;
		return true;
	end if;

	if vc lt 0 then
		return false;
	end if;

	if vr lt 0 then
		return false;
	end if;

	if not IsPower(c,l2) then
		return false;
	end if;

	if l2 eq 1 then
		return true;
	end if;

	// Hensel's lemma applied to X^l2 - (c + ra^l1) (note that c is an l2-th power)
	if Valuation(r,p) gt 2 * Valuation(l2,p) + 2 * (l2-1) / l2 * Valuation(c,p) then
		return true;
	end if;

	error "not implemented";
end intrinsic;


intrinsic Subdivide(N::PadNbhdElt, n::RngIntElt) -> SeqEnum
{Subdivides a p-adic nbhd N into nbhds of radius radius <= p^n}
	require Exponent(N) eq 1: "Argument 1 must be of the form c + r * OK";

	X := Parent(N);
	p := Prime(X);
	vr := Valuation(Radius(N),p);
	if n le vr then
		return [N];
	else
		OK := Integers(AmbientSpace(X));
		R := quo<OK | p^(n-vr)>;
		phi := Coercion(OK,R);

		//enumerating R can result in some duplicate elements,
		//so we will remove them first (this is fixed as per MAGMA V2.27-7)
		R_set := {y : y in R};

		c := Middle(N);
		pi := UniformizingElement(X);
		return [ pAdicNbhd(X, c + r * y@@phi, r * pi^(n-vr)) : y in R_set];
	end if;
end intrinsic;