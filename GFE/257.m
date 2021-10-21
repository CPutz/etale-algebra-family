Q := Rationals();
Z := Integers();

intrinsic Etale257(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
		Append(~E0s, E0);
	end for;

	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];

	F2 := SwitchVariables(Evaluate(Fs, 1 + p^2*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, D := D);
	E2 := [<E[1], [1 + p^2 * X!B : B in E[2]]> : E in E2];

	F3 := ReciprocalPolynomial(p^7 * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
	E3 := [<E[1], [Invert(p^7 * X!B) : B in E[2]]> : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
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

intrinsic Etale257_2(p::RngIntElt
	: D := LocalFieldDatabase()) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	printf "S3\n";
	//F3 := ReciprocalPolynomial(p^7 * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
	F3 := p^7 * 4*t^5*(25*t^3 + 20*s*t^2 + 14*s^2*t + 14*s^3) - s^7*(4*t - 1);
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);

	return E3;
end intrinsic;


intrinsic Etale357(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> .
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 15*t^7 - 35*t^6 + 21*t^5 - s;
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
		Append(~E0s, E0);
	end for;
	
	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];

	F2 := SwitchVariables(Evaluate(Fs, 1 + p^3*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(3)!0, D := D);
	E2 := [<E[1], [1 + p^2 * X!B : B in E[2]]> : E in E2];

	F3 := ReciprocalPolynomial(p^7 * s * (15*t^7 - 35*t^6 + 21*t^5) - 1);
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
	E3 := [<E[1], [Invert(p^7 * X!B) : B in E[2]]> : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
end intrinsic;





intrinsic Etale3511(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := (3*t^2 + t + 1)^5 * (1 - 5*t) - s;
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E0s := [];
	for a in [2..(p-1)] do
		F0 := SwitchVariables(Evaluate(Fs, a + p*t));
		E0 := EtaleAlgebraFamily(F0, p : D := D);
		E0 := [<E[1], [a + p * X!B : B in E[2]]> : E in E0];
		Append(~E0s, E0);
	end for;

	F1 := SwitchVariables(Evaluate(Fs, p^5*t));
	E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
	E1 := [<E[1], [p^5 * X!B : B in E[2]]> : E in E1];

	F2 := SwitchVariables(Evaluate(Fs, 1 + p^3*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(3)!0, D := D);
	E2 := [<E[1], [1 + p^3 * X!B : B in E[2]]> : E in E2];

	E2 := [];

	F3 := ReciprocalPolynomial(p^11 * s * t * (3*t^2 + 11*t + 33)^5 - 5^10);
	E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(11)!0, D := D);
	E3 := [<E[1], [Invert(p^11 * X!B) : B in E[2]]> : E in E3];

	Es := {@ @};
	Eis := E0s cat [E1,E2,E3];
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
end intrinsic;


intrinsic Etale257Unramified(p::RngIntElt
	: Neighbourhoods := false) -> SeqEnum
{}
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


intrinsic Etale257Other(p::RngIntElt
	: D := LocalFieldDatabase(),
	  Neighbourhoods := false) -> SeqEnum
{}
	S<s> := PolynomialRing(Rationals());
	R<t> := PolynomialRing(S);
	F := 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - s*(4*t - 1);
	Fs := SwitchVariables(F);

	K := pAdicField(p, 500);
	X := pAdicNbhds(K);

	E1s := [];
	for k in [1..4] do
		F1 := SwitchVariables(Evaluate(Fs, p^k*t));
		E1 := EtaleAlgebraFamily(F1, p : Filter := Integers(5)!0, D := D);
		E1 := [<E[1], [p^k * X!B : B in E[2]]> : E in E1];
		Append(~E1s, E1);
	end for;

	F2 := SwitchVariables(Evaluate(Fs, 1 + p*t));
	E2 := EtaleAlgebraFamily(F2, p : Filter := Integers(2)!0, D := D);
	E2 := [<E[1], [1 + p * X!B : B in E[2]]> : E in E2];

	E3s := [];
	for k in [1..6] do
		k;
		F3 := ReciprocalPolynomial(p^k * s * 4*t^5*(25*t^3 + 20*t^2 + 14*t + 14) - (4*t - 1));
		E3 := EtaleAlgebraFamily(F3, p : Filter := Integers(7)!0, D := D);
		E3 := [<E[1], [Invert(p^k * X!B) : B in E[2]]> : E in E3];
		Append(~E3s, E3);
	end for;
"combining";
	Es := {@ @};
	Eis := E1s cat [E2] cat E3s;
	for Ei in Eis do
		for E in Ei do
			Include(~Es, E[1]);
		end for;
	end for;

	EBs := {@ @};
	if Neighbourhoods then
		"neighbourhoods";
		for E in Es do
			Include(~EBs, <E, [B : B in EB[2], EB in Ei, Ei in Eis | EB[1] eq E]>);
		end for;
		Es := EBs;
	end if;

	return SetToSequence(Es);
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