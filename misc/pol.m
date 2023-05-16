AttachSpec("/home/cp/Git/etale-algebra-family/spec");

//product of L which is 1 if L is empty
function prod(L);
	if IsEmpty(L) then
		return 1;
	else
		return &*L;
	end if;
end function;

function RandomPolynomial(M,n,x);
	R := Parent(x);
	return x^n + R![Random(M) : i in [1..n]];
end function;

function RandomIrreduciblePolynomial(M,n,x,R);
	repeat
		f := RandomPolynomial(M, n, x);
	until IsIrreducible(PolynomialRing(R)!f);
	return f;
end function;

function test(d,k,m,p,vs0);
	n := d*k;

	R<x> := PolynomialRing(Rationals());

	//choose f to be irreducible over Q_p
	repeat
		f := RandomPolynomial(100, d, x);
	until IsIrreducible(PolynomialRing(pAdicField(p,500))!f);
	g := RandomPolynomial(100, m, x);

	assert Discriminant(f) ne 0;

	mu_f := Max([v[1] : v in ValuationsInRootsOf(Derivative(f), f, p)]);
	c := Valuation(Resultant(f, g) ^ (k - 1) * Discriminant(f) ^ k * k ^ n, p);

	"c", c * 1.;

	S<e,s,t> := PolynomialRing(Rationals(),3);
	F := f^k - p^vs0 * g;

	resdiff := Evaluate(Resultant(Resultant(e - (s - t), Evaluate(F,s), s), Evaluate(F,t), t), [x,0,0]);
	vs := [v : v in ValuationsOfRoots(resdiff, p) | v[1] lt Infinity()];

	maxdiff := Max([v[1] : v in vs]);
	"max diff: ", maxdiff * 1.;
	low := vs0 / k - mu_f;
	upp := vs0 / k - mu_f + (c / n - mu_f);
	upp2 := vs0 / k - mu_f + (1/d - 1/n) * Valuation(Resultant(f,g), p) + mu_f + Valuation(k,p);
	"lower, upper: ", low * 1., upp * 1., upp2 * 1.;
mu_f;
	maxdF := Max([v[1] : v in ValuationsInRootsOf(Derivative(F), F, p)]);

	return low le maxdiff, maxdiff le upp, maxdiff le upp2, maxdF eq c / n + (1 - 1/k) * vs0;
end function;

function test2(d,k,m,p);
	n := d*k;

	R<x> := PolynomialRing(Rationals());
	_<s,t> := PolynomialRing(Rationals(),2);

	//choose f to be irreducible over Q_p
	repeat
		f := RandomPolynomial(100, d, x);
	until IsIrreducible(PolynomialRing(pAdicField(p,500))!f);
	g := RandomPolynomial(100, m, x);

	assert Discriminant(f) ne 0;

	mu_f := Max([v[1] : v in ValuationsInRootsOf(Derivative(f), f, p)]);
	c := Valuation(Resultant(f, g) ^ (k - 1) * Discriminant(f) ^ k * k ^ n, p);
	creal := Coefficient(Evaluate(Discriminant(Evaluate(f,t)^k - s*Evaluate(g,t), t),[x,0]), n - d);

	assert Valuation(creal,p) eq c;
mu_f;
	return mu_f le c / n and c / n le 2*mu_f, c / n * 1., mu_f * 1., 2*mu_f * 1.;
end function;

function test3(d,k,m,p,vs0);
	n := d*k;

	R<x> := PolynomialRing(Rationals());
	_<s,t> := PolynomialRing(Rationals(),2);

	//choose f to be irreducible over Q_p
	repeat
		f := RandomPolynomial(100, d, x);
	until IsIrreducible(PolynomialRing(pAdicField(p,500))!f);
	g := RandomPolynomial(100, m, x);

	assert Discriminant(f) ne 0;

	F := f^k - p^vs0 * g;

	mu_f := Max([v[1] : v in ValuationsInRootsOf(Derivative(f), f, p)]);
	mu_F := Max([v[1] : v in ValuationsInRootsOf(Derivative(F), F, p)]);
	sig := Separant(F,p);
	c := Valuation(Coefficient(Evaluate(Discriminant(Evaluate(f,t)^k - s*Evaluate(g,t), t),[x,0]), n - d), p);
	assert mu_F eq c / n + vs0 * (1 - 1/k);
(vs0) + (c / n - mu_f) * 1., sig * 1., (vs0) + 2 * (c / n - mu_f) * 1.;
	return c / n - mu_f * 1., vs0 - mu_f * 1., (vs0) + (c / n - mu_f) le sig, sig le (vs0) + 2 * (c / n - mu_f);
end function;

function test4(d,k,m,p,vs0,del);
	n := d*k;

	R<x> := PolynomialRing(Rationals());
	_<s,t> := PolynomialRing(Rationals(),2);

	//choose f to be irreducible over Q_p
	repeat
		f := RandomPolynomial(100, d, x);
	until IsIrreducible(PolynomialRing(pAdicField(p,500))!f);
	g := RandomPolynomial(100, m, x);

	assert Discriminant(f) ne 0;

	F := f^k - p^vs0 * g;
	df := Derivative(f);

	_<e,alp,th> := PolynomialRing(Rationals(),3);
	res := Evaluate(
		Resultant(Resultant(e - (Evaluate(df,th) * (alp - th) - del * Evaluate(f,alp)), Evaluate(f,th), th), Evaluate(F,alp), alp),
		[x,0,0]);
	res2 := Evaluate(
		Resultant(Resultant(e - (Evaluate(df, th) - del * Evaluate(df, alp)), Evaluate(f,th), th), Evaluate(F,alp), alp),
		[x,0,0]);
	tau_F := Valuation(Coefficient(Evaluate(Discriminant(Evaluate(f,t)^k - s*Evaluate(g,t), t),[x,0]), n - d), p);
	mu_f := Max([v[1] : v in ValuationsInRootsOf(Derivative(f), f, p)]);

	ValuationsOfRoots(res,p);
	mdiff := Max([v[1] : v in ValuationsOfRoots(res,p)]);
	mdiff * 1., vs0 / k - mu_f * 1., vs0 / k - mu_f + tau_F / n - mu_f * 1.;

	efg := Max([v[1] : v in ValuationsInRootsOf(g, f, p)]);
	Max([v[1] : v in ValuationsOfRoots(res2,p)]) - mu_f;

	mdiff - mu_f gt vs0 / k + (tau_F / n - mu_f) / (k-1), mdiff - mu_f * 1., vs0 / k + (tau_F / n - mu_f) / (k-1) * 1.;

	return mdiff ge vs0 / k - mu_f, mdiff ge vs0 / k - mu_f + tau_F / n - mu_f;
end function;

function test5(d,k,m,p,vs0,del);
	n := d*k;

	R<x> := PolynomialRing(Rationals());
	_<s,t> := PolynomialRing(Rationals(),2);

	//choose f to be irreducible over Q_p
	f := RandomIrreduciblePolynomial(10, d, x, pAdicField(p,500));
	g := RandomPolynomial(10, m, x);

	assert Discriminant(f) ne 0;
	assert Resultant(f,g) ne 0;

	F := f^k - p^vs0 * g;
	df := Derivative(f);

	_<e,alp,th,phi> := PolynomialRing(Rationals(),4);
	dfth := Evaluate(df, th);
	res := Evaluate(
		Resultant(Resultant(Resultant(e - Evaluate(f^k - del^k * p^vs0 * g, phi),
			dfth * phi - (dfth * th + del * Evaluate(f,alp)), phi),
			Evaluate(f, th), th),
			Evaluate(F, alp), alp),
		[x,0,0,0]);
	sep := Separant(f^k - p^vs0 * g, p);

	m := Max([v[1] : v in ValuationsOfRoots(res,p)]);

	tau_F := Valuation(Coefficient(Evaluate(Discriminant(Evaluate(f,t)^k - s*Evaluate(g,t), t),[x,0]), n - d), p);
	mu_f := Max([v[1] : v in ValuationsInRootsOf(Derivative(f), f, p)]);

	resdiff := Evaluate(Resultant(Resultant(e - (alp - th), Evaluate(F,alp), alp), Evaluate(F,th), th), [x,0,0,0]);
	"root diffs: ", [v : v in ValuationsOfRoots(resdiff,p) | v[1] lt Infinity()];
	Max([v[1] : v in ValuationsOfRoots(resdiff,p) | v[1] lt Infinity()]) * 1.;
	guess := vs0 / k + tau_F / n - 2*mu_f;
	//guess := vs0 / k - mu_f + (tau_F / n - mu_f) / (k-1);
	"error: ", guess * 1. - Max([v[1] : v in ValuationsOfRoots(resdiff,p) | v[1] lt Infinity()]) * 1.;
	"tau_F / n - mu_f: ", tau_F / n - mu_f * 1.;
	"mu_f: ", mu_f;
	if tau_F / n - mu_f eq 0 then
		"error%: oo";
	else
		"error%: ", (guess - Max([v[1] : v in ValuationsOfRoots(resdiff,p) | v[1] lt Infinity()])) / (tau_F / n - mu_f);
	end if;
	guess * 1., vs0 * 1. / k - mu_f;

//#GaloisGroup(PolynomialRing(pAdicField(p,500))!F);
//#GaloisGroup(PolynomialRing(pAdicField(p,500))!f);

	return m gt sep, m gt 2 * (tau_F - mu_f) + vs0, m * 1., sep * 1., 2 * (tau_F - mu_f) + vs0 * 1., tau_F * 1.;
end function;

function test6(d,k,m,p,vs0,M);
	n := d*k;

	R<x> := PolynomialRing(Rationals());
	Qp := pAdicField(p,500);

	for i := 1 to M do
		f := RandomIrreduciblePolynomial(10, d, x, Qp);
		g := RandomPolynomial(10, m, x);
		F := PolynomialRing(Qp)!(f^k - p^vs0 * g);
		#GaloisGroup(F) eq Factorial(d*k);
	end for;
	return 0;
end function;

function test7(d,k,m,p,vs0,del);
	n := d*k;

	R<s,t> := PolynomialRing(Rationals(),2);
	_<z> := PolynomialRing(Rationals());
	Qp := pAdicField(p,500);

	f := RandomIrreduciblePolynomial(10, d, z, Qp);
	g := RandomPolynomial(10, m, z);
	F := Evaluate(f,t)^k - s * Evaluate(g,t);

ValuationsOfRoots(Evaluate(f,z)^k - p^vs0 * Evaluate(g,z),p);

	_<e,S,x,y> := PolynomialRing(Rationals(),4);
	res := Evaluate(
		Resultant(Resultant(e - (x-y), Evaluate(F,[S,x]),x),Evaluate(F,[S,y]),y),
		[t,s,0,0]);

	return ValuationsOfRoots(Evaluate(res,[p^vs0,z]),p),ValuationsOfRoots(Evaluate(res,[p^vs0*del^k,z]),p);
end function;

function splitting_field(F);
	K := BaseRing(F);
	M := K;
	r1 := Roots(F,M);
	while #r1 ne Degree(F) do
		RM<X> := PolynomialRing(M);
		Frest := (RM!F) div prod([(X - r[1])^r[2] : r in r1]);
		_,_,Ext := Factorization(Frest : Extensions := true);
		M := Ext[1]`Extension;
		r1 := Roots(F,M);
		#r1;
		Degree(M,K);
	end while;

	return M;
end function;

function test8(d,k,m,p,vs0,del);
	n := d*k;

	R<t> := PolynomialRing(Rationals());
	Qp := pAdicField(p,5000);
	Rp := PolynomialRing(Qp);

	f := RandomIrreduciblePolynomial(10, d, t, Qp);
	df := Derivative(f);
	g := RandomPolynomial(10, m, t);
	F := f^k - p^vs0 * g;
	F2 := f^k - del^k * p^vs0 * g;

	f,g;

	//time S := SplittingField(F);
	//S;

	K := Qp;
	//_,_,Ext := Factorization(Rp!f : Extensions:=true);
	//K := Ext[1]`Extension;

	//_,_,Ext2 := Factorization(PolynomialRing(K)!F : Extensions:=true);
	//L := Ext2[1]`Extension;

	/*_,_,Ext3 := Factorization(PolynomialRing(K)!F : Extensions := true);
	M1 := Ext3[1]`Extension;

	_,_,Ext4 := Factorization(PolynomialRing(M1)!F : Extensions := true);
	M2 := [E : E in Ext4 | Degree(E`Extension) gt 1][1]`Extension;
	M := M2;*/

	//create a splitting field for F
	M := K;
	r1 := Roots(F,M);
	while #r1 ne Degree(F) do
		RM<X> := PolynomialRing(M);
		Frest := (RM!F) div prod([(X - r[1])^r[2] : r in r1]);
		_,_,Ext := Factorization(Frest : Extensions := true);
		M := Ext[1]`Extension;
		r1 := Roots(F,M);
		#r1;
		Degree(M,Qp);
	end while;

	printf "splitting field computed\n";

	rf := [r[1] : r in Roots(f,M)];
	r1 := [r[1] : r in r1];
	r2 := [r[1] : r in Roots(F2,M)];

	assert #r1 eq Degree(F);
	#rf, "roots of f";
	#r2, "roots of F2";

	L := [];
	for i := 1 to #r1 do
		alp := r1[i];

		//get the unique theta closest to alpha
		max_th := Max([Valuation(alp - r) : r in rf]);
		#[r : r in rf | Valuation(alp - r) eq max_th];
		assert #[r : r in rf | Valuation(alp - r) eq max_th] eq 1;
		th := [r : r in rf | Valuation(alp - r) eq max_th][1];

		phi := th + del * Evaluate(f, alp) / Evaluate(df, th);

		//get the unique beta closest to phi
		max_bet := Max([Valuation(phi - r) : r in r2]);
		"differences", [Valuation(phi - r) : r in r2];
		"separant", Separant(F2,p);
		"evaluate", Valuation(Evaluate(F2,phi));
		#[r : r in r2 | Valuation(phi - r) eq max_bet];
		assert #[r : r in r2 | Valuation(phi - r) eq max_bet] eq 1;
		bet := [r : r in r2 | Valuation(phi - r) eq max_bet][1];

		//bet := phi;

		phi2 := th + del^(-1) * Evaluate(f, bet) / Evaluate(df, th);

		//get the unique alpha2 closest to phi2
		max_alp2 := Max([Valuation(phi2 - r) : r in r1]);
		#[r : r in r1 | Valuation(phi2 - r) eq max_alp2];
		assert #[r : r in r1 | Valuation(phi2 - r) eq max_alp2] eq 1;
		alp2 := [r : r in r1 | Valuation(phi2 - r) eq max_alp2][1];

		Append(~L, <alp,bet,alp2>);
	end for;

	return forall {c : c in L | c[1] eq c[3]};

	//return L;
end function;

function test8b(f,k,g,S,p,vs0,del);
	d := Degree(f);
	m := Degree(g);
	n := d*k;

	R<t> := PolynomialRing(Rationals());
	Qp := pAdicField(p,50000);
	Rp := PolynomialRing(Qp);

	df := Derivative(f);
	F := f^k - p^vs0 * g;
	F2 := f^k - del^k * p^vs0 * g;

	//a splitting field for F
	M := S;

	rf := [r[1] : r in Roots(f,M)];
	r1 := [r[1] : r in Roots(F,M)];
	r2 := [r[1] : r in Roots(F2,M)];

	assert #r1 eq Degree(F);
	#rf, "roots of f";
	#r2, "roots of F2";

	L := [];
	phis := [];
	phi2s := [];
	betas := [];
	for i := 1 to #r1 do
		alp := r1[i];

		//get the unique theta closest to alpha
		max_th := Max([Valuation(alp - r) : r in rf]);
		#[r : r in rf | Valuation(alp - r) eq max_th];
		assert #[r : r in rf | Valuation(alp - r) eq max_th] eq 1;
		th := [r : r in rf | Valuation(alp - r) eq max_th][1];

		phi := th + del * Evaluate(f, alp) / Evaluate(df, th);

		"v(g(th) - g(alp)) = ", Valuation(Evaluate(g, th) - Evaluate(g, alp));
		"v(th - alp) = ", Valuation(th - alp);
		eps := del * Evaluate(f, alp) / Evaluate(df, th);
		"v(error) = ", Valuation(Evaluate(df,th)^k * eps^k - p^vs0 * del^k * Evaluate(g,th));
		"v(f(th)) = ", Valuation(Evaluate(f,th));
		"v(eps) = ", Valuation(eps);
		taylor := [Evaluate(Derivative(F2,i) / Factorial(i),th) * eps^i : i in [0..2*k]];
		"v(taylor) = ", [Valuation(term) : term in taylor];
		"v(taylor_0 + taylor_k) = ", Valuation(taylor[1] + taylor[k+1]);

		//get the unique beta closest to phi
		max_bet := Max([Valuation(phi - r) : r in r2]);
		"differences", [Valuation(phi - r) : r in r2];
		"differences beta", [Valuation(rt1 - rt2) : rt1,rt2 in r2];
		"separant", 18 * Separant(F2,p);
		"evaluate", Valuation(Evaluate(F2,phi));
		"evaluate dF", Valuation(Evaluate(Derivative(F2),phi));
		#[r : r in r2 | Valuation(phi - r) eq max_bet];
		assert #[r : r in r2 | Valuation(phi - r) eq max_bet] eq 1;
		bet := [r : r in r2 | Valuation(phi - r) eq max_bet][1];

		phi_newton := phi - Evaluate(F2,phi) / Evaluate(Derivative(F2),phi);
		"difference beta = ", Valuation(bet - phi);
		"difference beta (newton) = ", Valuation(bet - phi_newton);
		"evaluate newton = ", Valuation(Evaluate(F2, phi_newton));
		"valuation diff newton = ", Valuation(Evaluate(F2,phi) / Evaluate(Derivative(F2),phi));

		"valuation dF(bet) = ", Valuation(Evaluate(Derivative(F2),bet));

		Append(~phis, phi);
		
		Append(~betas, bet);

		phi_newton2 := phi_newton - Evaluate(F2,phi_newton) / Evaluate(Derivative(F2),phi_newton);
		"difference beta = ", Valuation(bet - phi_newton);
		"difference beta (newton2) = ", Valuation(bet - phi_newton2);
		"evaluate newton2 = ", Valuation(Evaluate(F2, phi_newton2));
		"valuation diff newton = ", Valuation(Evaluate(F2,phi_newton) / Evaluate(Derivative(F2),phi_newton));
		Append(~phi2s, phi_newton2);
		/*T := FunctionField(Rationals());
		nn := 5;
		correction := (nn - 1) * Derivative(1 / T!F2, nn-2) / Derivative(1 / T!F2, nn-1);
		num := R!Numerator(correction);
		denom := R!Denominator(correction);
		phi_newton2 := phi - Valuation(Evaluate(num,phi)) div Valuation(Evaluate(denom,phi));
		"difference beta (newton2) = ", Valuation(bet - phi_newton2);
		"evaluate newton2 = ", Valuation(Evaluate(F2, phi_newton2));*/

		//bet := phi;

		phi2 := th + del^(-1) * Evaluate(f, bet) / Evaluate(df, th);

		//get the unique alpha2 closest to phi2
		max_alp2 := Max([Valuation(phi2 - r) : r in r1]);
		#[r : r in r1 | Valuation(phi2 - r) eq max_alp2];
		assert #[r : r in r1 | Valuation(phi2 - r) eq max_alp2] eq 1;
		alp2 := [r : r in r1 | Valuation(phi2 - r) eq max_alp2][1];

		Append(~L, <alp,bet,alp2>);
	end for;

	R<X> := PolynomialRing(S);
	F2g1 := &*[X - phi : phi in phis];
	F2g2 := &*[X - phi : phi in phi2s];
	F2g3 := &*[X - phi : phi in betas];

	"diffs guess 1 = ", [Valuation(c) : c in Coefficients(F2g1 - F2)];
	"diffs guess 2 = ", [Valuation(c) : c in Coefficients(F2g2 - F2)];
	"diffs sanity check = ", [Valuation(c) : c in Coefficients(F2g3 - F2)];

	return forall {c : c in L | c[1] eq c[3]};

	//return L;
end function;

function test9(d,k,m,p,vs0,del);
	n := d*k;

	R<t> := PolynomialRing(Rationals());
	Qp := pAdicField(p,5000);
	Rp := PolynomialRing(Qp);

	f := RandomIrreduciblePolynomial(10, d, t, Qp);
	df := Derivative(f);
	g := RandomPolynomial(10, m, t);
	F := f^k - p^vs0 * g;
	F2 := f^k - del^k * p^vs0 * g;

	//time S := SplittingField(F);
	//S;

	K := Qp;
	//_,_,Ext := Factorization(Rp!f : Extensions:=true);
	//K := Ext[1]`Extension;

	//_,_,Ext2 := Factorization(PolynomialRing(K)!F : Extensions:=true);
	//L := Ext2[1]`Extension;

	_,_,Ext3 := Factorization(PolynomialRing(K)!F : Extensions := true);
	M := Ext3[1]`Extension;

	rf := [r[1] : r in Roots(f,M)];
	r1 := [r[1] : r in Roots(F,M)];
	r2 := [r[1] : r in Roots(F2,M)];

	assert #r1 eq n;
	assert #rf eq d;

	S<X> := PolynomialRing(M);

	/*//rsnew := [Roots(Evaluate(f,X)^k - p^vs0 * Evaluate(g,th),M) : th in rf];

	L := [];
	for th in rf do
		rs := Roots(Evaluate(f,X)^k - p^vs0 * Evaluate(g,th),M);
		for r in rs do
			phi := th - del * Evaluate(f,r[1]) / Evaluate(df,th);
			Append(~L,phi);
		end for;
	end for;

	F2guess := &*[X - phi : phi in L];

	return F,F2,F2guess;*/

	L := [];
	for i := 1 to #r1 do
		alp := r1[i];

		//get the unique theta closest to alpha
		max_th := Max([Valuation(alp - r) : r in rf]);
		assert #[r : r in rf | Valuation(alp - r) eq max_th] eq 1;
		th := [r : r in rf | Valuation(alp - r) eq max_th][1];

		phi := th - del * Evaluate(f, alp) / Evaluate(df, th);

		//max_bet := Max([Valuation(phi - r) : r in r2]);
		//assert #[r : r in r2 | Valuation(phi - r) eq max_bet] eq 1;
		//bet := [r : r in r2 | Valuation(phi - r) eq max_bet][1];

		Append(~L, phi);
	end for;

	dF2 := Derivative(F2);
	return Separant(F2,p), [Valuation(Evaluate(F2, phi)) : phi in L], [Valuation(Evaluate(dF2, phi)) : phi in L];

	//F2guess := &*[X - phi : phi in L];

	//return F,F2,F2guess;
end function;

function test9(n,p);

end function;