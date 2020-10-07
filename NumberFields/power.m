Z := Integers();
Q := Rationals();

intrinsic GeneralNormMatrix(L::FldNum) -> SeqEnum
{}
	K := BaseField(L);
	B := Basis(L);
	R := PolynomialRing(L, #B);
	f := &+[R.i * B[i] : i in [1..#B]];
	C,M := CoefficientsAndMonomials(f);

	S := PolynomialRing(K, #B);
	res := ZeroMatrix(S,#B,#B);
	for i := 1 to #C do
		c := C[i];
		m := M[i];
		X := Parent(res)!RepresentationMatrix(c);
		res +:= X * m;
	end for;

	return res;
end intrinsic;

intrinsic TorsionBound(J::JacHyp[FldNum[FldRat]], n::RngIntElt) -> RngIntElt
{}	
	K := BaseRing(J);
	S := BadPrimes(J);
	for P in PrimesUpTo(20) do
		D := Decomposition(K,P);
		for pl in D do
			p := Ideal(pl[1]);
			if p notin S then
				f := HyperellipticPolynomials(Curve(J));
				F,map1 := ResidueClassField(p);
				OK := Domain(map1);
				R := PolynomialRing(OK);
				_,map2 := ChangeRing(R,F,map1);
				fp := map2(R!f);
				Cp := HyperellipticCurve(fp);
				Jp := Jacobian(Cp);
				#RationalPoints(Jp);
			end if;
		end for;
	end for;

	return 0;
end intrinsic;

intrinsic GCDPID(x::FldNumElt, y::FldNumElt) -> FldNumElt
{}
	K := Parent(x);
	require Parent(y) eq K: "Argument 1 and 2 must have the same parent";
	require ClassNumber(K) eq 1: "K must have class number 1";

	Nx := Norm(x);
	Ny := Norm(y);
	N := GCD(Z!Nx, Z!Ny);

	g := K!1;
	for P in PrimeDivisors(N) do
		DP := Decomposition(K, P);
		for p in DP do
			vx := Valuation(x, p[1]);
			vy := Valuation(y, p[1]);
			_,gp := IsPrincipal(Ideal(p[1]));
			g *:= gp^Min(vx, vy);
		end for;
	end for;

	return g;
end intrinsic;

intrinsic GCDPIDMod2(x::FldNumElt, y::FldNumElt) -> FldNumElt
{}
	K := Parent(x);
	require Parent(y) eq K: "Argument 1 and 2 must have the same parent";
	require ClassNumber(K) eq 1: "K must have class number 1";

	Nx := Norm(x);
	Ny := Norm(y);
	N := GCD(Z!Nx, Z!Ny);

	g := K!1;
	for P in PrimeDivisors(N) do
		DP := Decomposition(K, P);
		for p in DP do
			vx := Valuation(x, p[1]);
			vy := Valuation(y, p[1]);
			_,gp := IsPrincipal(Ideal(p[1]));
			m := Min(vx, vy);
			if IsOdd(m) then
				m -:= 1;
			end if;
			g *:= gp^m;
		end for;
	end for;

	return g;
end intrinsic;

intrinsic GCDPIDMod2(L::SeqEnum) -> FldNumElt
{}
	x := L[1];
	for i := 2 to #L do
		x := GCDPIDMod2(x, L[i]);
	end for;
	return x;
end intrinsic;

intrinsic HyperellipticCurveReduceMod2(C::CrvHyp) -> CrvHyp
{}
	f := HyperellipticPolynomials(C);
	g := GCDPIDMod2(Coefficients(f));
	return HyperellipticCurve(f / g);
end intrinsic;