Q := Rationals();
Z := Integers();

intrinsic Etale257(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(SwitchVariables(F), a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		for i := 1 to #E0 do
			SetData(~E0[i], [a + p * B : B in Data(E0[i])]);
		end for;
		Append(~E0s, E0);
	end for;

	E1 := EtaleAlgebraFamily(F, p :
		MinVal := 5, CongrVal := Integers(5)!0, D := D, Precision := 400);

	F2 := SwitchVariables(Evaluate(SwitchVariables(F), 1 + t));
	E2 := EtaleAlgebraFamily(F2, p :
		MinVal := 2, CongrVal := Integers(2)!0, D := D, Precision := 400);
	for i := 1 to #E2 do
		SetData(~E2[i], [1 + B : B in Data(E2[i])]);
	end for;

	F3 := ReciprocalPolynomial(s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	E3 := EtaleAlgebraFamily(F3, p :
		MinVal := 7, CongrVal := Integers(7)!0, D := D, Precision := 400);
	for i := 1 to #E3 do
		SetData(~E3[i], [Invert(B) : B in Data(E3[i])]);
	end for;

	Es := [];
	Eis := (&cat E0s) cat E1 cat E2 cat E3;
	if not Neighbourhoods then
		for i := 1 to #Eis do
			ClearData(~Eis[i]);
		end for;
	end if;

	for Ei in Eis do
		if exists (i) {i : i in [1..#Es] | IsIsomorphic(Es[i], Ei)} then
			if Neighbourhoods then
				AddData(~Es[i], Data(Ei));
			end if;
		else
			Append(~Es, Ei);
		end if;
	end for;

	return Es;
end intrinsic;

intrinsic Etale257Linear(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	Es := Etale257(p : D := D);
	Es := [<RemoveLinearFactor(E[1]), E[2]> : E in Es | ContainsLinearFactor(E[1])];

	return Es;
end intrinsic;

intrinsic ContainsLinearFactor(E::EtAlg) -> BoolElt
{Returns true if E contains a linear factor}
	return HasRoot(DefiningPolynomial(E));
end intrinsic;

intrinsic RemoveLinearFactor(E::EtAlg) -> EtAlg
{Provided an etale algebra E with a linear factor, remove it}
	Cs := Components(E);
	Csnew := [];
	for C in Cs do
		if AbsoluteDegree(C[1]) eq 1 then
			if C[2] gt 1 then
				Append(~Csnew, <C[1], C[2]-1>);
			end if;
		else
			Append(~Csnew, C);
		end if;
	end for;
	return EtaleAlgebra(Csnew);
end intrinsic;


intrinsic Etale257Unramified(p::RngIntElt
	: Neighbourhoods := false) -> SeqEnum
{}
	require p notin [2,5,7]: "Argument 1 must be unequal to 2, 5 or 7";
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	S<x> := PolynomialRing(pAdicField(p,500));
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;

	Es := [];
	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *},Q!a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *}, p^5 * a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *}, 1 + p^2 * a>);
	end for;

	for a in [2..(p-1)] do
		Append(~Es, <{* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *}, p^(-7) * a>);
	end for;

	Eis := {@ E[1] : E in Es @};
	if not Neighbourhoods then
		return Eis;
	else
		return {@ <E, {@ F[2] : F in Es | F[1] eq E @}> : E in Eis @};
	end if;
end intrinsic;

intrinsic Etale257Unramified2(p::RngIntElt) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum
{}
	R<t> := PolynomialRing(GF(p));
	psi := 25*t^3 + 20*t^2 + 14*t + 14;
	phi := 4*t^5 * psi;

	S<x> := PolynomialRing(pAdicField(p,500));
	Phi := 10*x^4 + 4*x^3 + 2*x^2 + 2*x - 1;


	Es := AssociativeArray();
	for a in [2..(p-1)] do
		par := {* Degree(f[1])^^f[2] : f in Factorization(phi - a * (4*t - 1)) *};
		if IsDefined(Es, par) then
			Append(~Es[par], GF(p)!a);
		else
			Es[par] := [GF(p)!a];
		end if;
	end for;

	Es0 := AssociativeArray();
	for a in [2..(p-1)] do
		par := {* Degree(f[1])^^f[2] : f in Factorization(psi * (t^5 - a)) *};
		if IsDefined(Es0, par) then
			Append(~Es0[par], GF(p)!a);
		else
			Es0[par] := [GF(p)!a];
		end if;
	end for;

	Es1 := AssociativeArray();
	for a in [2..(p-1)] do
		par := {* Degree(f[1])^^f[2] : f in Factorization(Phi^2 - a*p^2*(4*x-1)) *};
		if IsDefined(Es1, par) then
			Append(~Es1[par], GF(p)!a);
		else
			Es1[par] := [GF(p)!a];
		end if;
	end for;

	Esoo := AssociativeArray();
	for a in [2..(p-1)] do
		par := {* Degree(f[1])^^f[2] : f in Factorization(t * (t^7 - a)) *};
		if IsDefined(Esoo, par) then
			Append(~Esoo[par], GF(p)!a);
		else
			Esoo[par] := [GF(p)!a];
		end if;
	end for;

	return Es, Es0, Es1, Esoo;
end intrinsic;


intrinsic FactorizationPartition(f::RngUPolElt, p::RngIntElt) -> SetMulti
{}
	Rp := PolynomialRing(pAdicField(p,500));
	fac := Factorization(Rp!f);
	return {* Degree(d[1])^^d[2] : d in fac *};
end intrinsic;

intrinsic FindParameter() -> .
{}
	Dx := [5];
	Dz := [];
	Dy := [2];

	R<t> := PolynomialRing(Q);
	f := t^8 + 2*t^7 + 56*t^6 + 140*t^5 - 560*t^4 + 7504*t^3 + 26348*t^2 + 24204*t + 3510;

	gen := [11, 17, 29, 197, 373, 1307, 7^4];
	congr := [[7], [3,5,8,10], [9,23], [177], [98,145,345], [419,758,818,1093], [7^3,-7^3]];
	/*congr := [];
	for p in gen do
		p;
		E,E0,E1,Eoo := Etale257Unramified2(p);
		par := FactorizationPartition(f, p);

		assert par notin Keys(E0) join Keys(E1) join Keys(Eoo);
		Append(~congr, [Z!c : c in E[par]]);
	end for;*/

	B := 100;
	primes := [p : p in PrimesUpTo(B) | p notin [2,5,7] cat gen];
	for p in primes do
		p;
		E,E0,E1,Eoo := Etale257Unramified2(p);
		par := FactorizationPartition(f, p);
		if par in Keys(E0) then
			Append(~Dx, p);
		end if;
		if par in Keys(E1) then
			Append(~Dy, p);
		end if;
		if par in Keys(Eoo) then
			Append(~Dz, p);
		end if;
	end for;

	Dx;
	Dz;

	M := 3;
	num   := [(&*[Dx[i]^k[i] : i in [1..#Dx]])^5 : k in CartesianPower([0..M],#Dx)];
	denom := [(&*[Dz[i]^k[i] : i in [1..#Dz]])^7 : k in CartesianPower([0..M],#Dz)];

	Car := CartesianProduct(congr);
	//C := [ChineseRemainderTheorem(TupSeq(c),gen) : c in Car];

	C := [n / d * ChineseRemainderTheorem([Z!(Integers(gen[i])!d/n * c[i]) : i in [1..#gen]], gen) : c in Car, d in denom, n in num];

	B2 := 200;
	primesfilter := [p : p in PrimesUpTo(B2) | p notin [2,5,7] cat gen cat primes];
	for p in primesfilter do
		p;
		#C;
		E,E0,E1,Eoo := Etale257Unramified2(p);
		par := FactorizationPartition(f, p);
		
		Cnew := [];
		for c in C do
			v := Valuation(c,p);
			if v gt 0 then
				if v mod 5 eq 0 and par in Keys(E0) then
					Append(~Cnew, c);
				end if;
			elif v lt 0 then
				if v mod 7 eq 0 and par in Keys(Eoo) then
					Append(~Cnew, c);
				end if;
			else
				v1 := Valuation(1-c, p);
				if v1 gt 0 and par in Keys(E1) then
					Append(~Cnew, c);
				else
					if par in Keys(E) and Z!GF(p)!c in E[par] then
						Append(~Cnew, c);
					end if;
				end if;
			end if;
		end for;
		C := Cnew;

		if IsEmpty(C) then
			break;
		end if;
	end for;

	return C;
end intrinsic;

