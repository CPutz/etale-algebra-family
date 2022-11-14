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

intrinsic HyperellipticReduction(C::CrvHyp, p::RngOrdIdl) -> CrvHyp
{}
	K := BaseRing(C);
	f := HyperellipticPolynomials(C);
	F,map1 := ResidueClassField(p);
	OK := Domain(map1);
	R := PolynomialRing(OK);
	_,map2 := ChangeRing(R,F,map1);
	fp := map2(R!f);
	return HyperellipticCurve(fp);
end intrinsic;

intrinsic TorsionBound(J::JacHyp[FldNum[FldRat]], n::RngIntElt) -> RngIntElt
{}	
	K := BaseRing(J);
	S := BadPrimes(J);
	for P in PrimesUpTo(n) do
		D := Decomposition(K,P);
		for pl in D do
			p := Ideal(pl[1]);
			if p notin S and InertiaDegree(pl[1]) eq 1 then
				C := Curve(J);
				Cp := HyperellipticReduction(C,p);
				Jp := Jacobian(Cp);
				//p;
				//#RationalPoints(Cp);
				#RationalPoints(Jp);
			end if;
		end for;
	end for;

	return -1;
end intrinsic;

intrinsic NormalizeHyperellipticCurve(C::CrvHyp[FldNum]) -> CrvHyp
{}
	f,g := HyperellipticPolynomials(C);
	require g eq 0: "Argument 1 must be of the form y^2 = f(x)";
	x := Parent(f).1;
	n := Degree(f);
	c0 := LeadingCoefficient(f);
	K := Parent(c0);

	for P in PrimeDivisors(Z!Norm(c0)) do
		DP := Decomposition(K, P);
		for p in DP do
			v := Valuation(c0, p[1]);
			_,gp := IsPrincipal(Ideal(p[1]));
			if IsOdd(v) then
				v +:= 5;
				f := Evaluate(f, x * gp);
			end if;
			f *:= gp^(-v);
		end for;
	end for;

	// Only works in my specific example
	c0 := ConstantCoefficient(f);
	for P in PrimeDivisors(Denominator(Norm(c0)) * Numerator(Norm(c0))) do
		DP := Decomposition(K, P);
		for p in DP do
			v := Valuation(c0, p[1]);
			k := (Z!v) mod 10;
			l := (v - k) div 10;
			_,gp := IsPrincipal(Ideal(p[1]));
			f := Evaluate(f, x * gp^(2*l));
			f *:= gp^(-10*l);
		end for;
	end for;

	c0 := LeadingCoefficient(f);
	assert Norm(c0) in {1, -1};

	G,fG := UnitGroup(K);
	e := fG(G.2);

	k := 0;
	found := false;
	while not found do
		if e^k eq c0 then
			if IsEven(k) then
				f *:= e^(-k);
			else
				f := Evaluate(f, x * e);
				f *:= e^(-k-5);
			end if;
			found := true;
		elif e^(-k) eq c0 then
			if IsEven(k) then
				f *:= e^(k);
			else
				f := Evaluate(f, x * e);
				f *:= e^(k-5);
			end if;
			found := true;
		elif -e^(k) eq c0 then
			f := Evaluate(f, -x);
			if IsEven(k) then
				f *:= e^(-k);
			else
				f := Evaluate(f, x * e);
				f *:= e^(-k-5);
			end if;
			found := true;
		elif -e^(-k) eq c0 then
			f := Evaluate(f, -x);
			if IsEven(k) then
				f *:= e^(k);
			else
				f := Evaluate(f, x * e);
				f *:= e^(k-5);
			end if;
			found := true;
		end if;
		
		k +:= 1;
	end while;

	return HyperellipticCurve(f);
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