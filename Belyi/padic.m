Q := Rationals();
Z := Integers();

function lifts(fs, x, J, p);
	vfx := Min([Valuation(Evaluate(f,x),p) : f in fs]);
	vJ := Valuation(Determinant(J),p);
	if vJ lt vfx then
		vfx, vJ;
	end if;
	return vJ lt vfx;
end function;

intrinsic HenselLift(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt], max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	MQ := MatrixAlgebra(Q,n);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	J := JacobianMatrix(Eltseq(fs));

	xs := [x0];

	for k := 1 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^(2^k));
			Rpe := RSpace(Zpe,n);

			Jx := Transpose(Evaluate(J, x));
			//inv,Jxi := IsInvertible(Jx);
			
			target := -RSpace(Parent(x[1]),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(2^(k-1)));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				if Dimension(Ker) eq 0 then
					xnew := Eltseq(Rpe!RZ!x + p^(2^(k-1))*Rpe!RZ!(y));
					Append(~xsnew, xnew);
				else
					for y0 in Ker do
						xnew := Eltseq(Rpe!RZ!x + p^(2^(k-1))*Rpe!RZ!(y+y0));
						Append(~xsnew, xnew);
					end for;
				end if;
			end if;
		end for;
		xs := xsnew;
		//#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLift(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt],
	xs0::SeqEnum, pstart::RngIntElt, max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	MQ := MatrixAlgebra(Q,n);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	J := JacobianMatrix(Eltseq(fs));

	xs := xs0;

	for k := 1 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^(pstart*2^k));
			Rpe := RSpace(Zpe,n);

			Jx := Transpose(Evaluate(J, x));
			
			target := -RSpace(Parent(x[1]),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(pstart*2^(k-1)));

			if IsConsistent(Jx, target) then
				Append(~xsnew, x);
				/*y,Ker := Solution(Jx, target);
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(pstart*2^(k-1))*Rpe!RZ!(y+y0));
					Append(~xsnew, xnew);
				end for;*/
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftLinear(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt], max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	Mp := RMatrixSpace(GF(p),n,m);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	
	xs := [x0];
	Jx := Mp!Transpose(Evaluate(JacobianMatrix(Eltseq(fs)), x0));
	Kernel(Jx);


	for k := 2 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^k);
			Rpe := RSpace(Zpe,n);

			target := -RSpace(GF(p),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!RZ!(y+y0));
					Append(~xsnew, xnew);
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftLinear(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt],
	xs0::SeqEnum, pstart::RngIntElt, max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	Mp := RMatrixSpace(GF(p),n,m);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	
	xs := xs0;
	Jx := Mp!Transpose(Evaluate(JacobianMatrix(Eltseq(fs)), x0));
	Kernel(Jx);


	for k := pstart+1 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^k);
			Rpe := RSpace(Zpe,n);

			target := -RSpace(GF(p),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!RZ!(y+y0));
					Append(~xsnew, xnew);
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftHybrid(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt],
		swit::RngIntElt, max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	MQ := MatrixAlgebra(Q,n);
	Mp := RMatrixSpace(GF(p),n,m);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	J := JacobianMatrix(Eltseq(fs));

	xs := [x0];

	for k := 1 to swit do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^(2^k));
			Rpe := RSpace(Zpe,n);

			Jx := Transpose(Evaluate(J, x));
			target := -RSpace(Parent(x[1]),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(2^(k-1)));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(2^(k-1))*Rpe!RZ!(y+y0));
					Append(~xsnew, xnew);
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	Jx := Mp!Transpose(Evaluate(JacobianMatrix(Eltseq(fs)), x0));
	Kernel(Jx);

	for k := 2^swit+1 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^k);
			Rpe := RSpace(Zpe,n);

			target := -RSpace(GF(p),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!RZ!(y+y0));
					Append(~xsnew, xnew);
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftHybridFilter(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt],
	max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	Mp := RMatrixSpace(GF(p),n,m);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	
	xs := [x0];
	J := Transpose(JacobianMatrix(Eltseq(fs)));
	Jx := Mp!Evaluate(J, x0);
	Kernel(Jx);


	for k := 2 to max do
		xsnew := [];
		Zpe := Integers(p^k);
		Rpe := RSpace(Zpe,n);
		Rpem := RSpace(Zpe,m);
		for x in xs do
			target := -RSpace(GF(p),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!RZ!(y+y0));
					//if IsOdd(k) then
						Jx2 := Evaluate(J, xnew);
						target2 := -Rpem!(Evaluate(fs, Eltseq(RZ!xnew)) div p^k);
						if IsConsistent(Jx2, target2) then
							Append(~xsnew, xnew);
						end if;
					//else
					//	Append(~xsnew, xnew);
					//end if;
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftFilter(fs::SeqEnum[RngMPolElt], x0::SeqEnum[FldFinElt], max::RngIntElt) -> .
{}
	n := #x0;
	m := #fs;
	p := Characteristic(Parent(x0[1]));
	RZ := RSpace(Z,n);
	Rp := RSpace(GF(p),n);
	MQ := MatrixAlgebra(Q,n);

	fs := RSpace(Parent(fs[1]), #fs)!fs;
	J := JacobianMatrix(Eltseq(fs));

	xs := [x0];

	for k := 1 to max do
		xsnew := [];
		for x in xs do
			Zpe := Integers(p^(2^k));
			Rpe := RSpace(Zpe,n);

			Jx := Transpose(Evaluate(J, x));
			
			target := -RSpace(Parent(x[1]),m)!(Evaluate(fs, Eltseq(RZ!x)) div p^(2^(k-1)));

			hassol, y, Ker := IsConsistent(Jx, target);
			if hassol then
				for y0 in Ker do
					xnew := Eltseq(Rpe!RZ!x + p^(2^(k-1))*Rpe!RZ!(y+y0));
					target2 := -RSpace(Parent(xnew[1]),m)!(Evaluate(fs, Eltseq(RZ!xnew)) div p^(2^k));
					Jx2 := Transpose(Evaluate(J, xnew));
					if IsConsistent(Jx2, target2) then
						Append(~xsnew, xnew);
					end if;
				end for;
			end if;
		end for;
		xs := xsnew;
		#xs;
	end for;

	return xs;
end intrinsic;

intrinsic HenselLiftLinear2(fs::SeqEnum[RngMPolElt], x::SeqEnum[FldFinElt], m::RngIntElt) -> .
{}
	p := Characteristic(Parent(x[1]));
	RZ := RSpace(Z,7);
	Rp := RSpace(GF(p),7);
	Mp := MatrixAlgebra(GF(p),7);

	fs := RSpace(Parent(fs[1]), #fs)!fs;

	Jx := Mp!Evaluate(JacobianMatrix(Eltseq(fs)), x);
	b,Jxi := IsInvertible(Jx);

	Jxi := Transpose(Jxi);
	
	for k := 2 to m do
		Zpe := Integers(p^k);
		Rpe := RSpace(Zpe, 7);
		y := RZ!(Rp!-(Evaluate(fs, Eltseq(RZ!x)) div p^(k-1)) * Jxi);
		x := Eltseq(Rpe!RZ!x + p^(k-1)*Rpe!y);
	end for;

	return x;
end intrinsic;

intrinsic FindAlgebraicRelation(a::., p::RngIntElt, n::RngIntElt, B::RngIntElt, N::RngIntElt) -> .
{}
	R := RMatrixSpace(Z, n+1, n+2);

	//build matrix
	M := R!0;
	for i := 1 to n+1 do M[i][1] := N*Z!a^(n-i+1); end for;
	for i := 1 to n+1 do M[i][i+1] := 1; end for;

	return LLL(M, p, B, N);
end intrinsic;

intrinsic ExampleSijsling(p::RngIntElt, m::RngIntElt) -> .
{}
	R<a,b,c,d,e,f,g> := PolynomialRing(Z,7);
	_<y> := PolynomialRing(R);

	F := a * (y^2 + b*y + c)^3 * (y - 1);
	G := y;
	H := a * (y^3 + d*y^2 + e*y + f)^2 * (y - g);

	fs := Coefficients(F - G - H);
	
	A := AffineSpace(GF(p),7);
	S := Scheme(A, fs);

	Ps := RationalPoints(S);

	return fs,HenselLift(fs, Eltseq(Ps[1]), m);
end intrinsic;

intrinsic ExampleRoberts2(p::RngIntElt) -> .
{}
	R<a,b,c,d,e,f,x> := PolynomialRing(Z,7);
	_<y> := PolynomialRing(R);

	F := a * y^6 * (y-1)^4 * (y-x)^2;
	G := (y-b)^3 * (y^2 + c*y + d)^2;
	//H := a*(y^5 + e*y^4 + f*y^3 + g*y^2 + h*y + i)^2 * (y^2 + j*y + k);

	Fd := Factorization(Derivative(F) * G - Derivative(G) * F)[7,1];
	Fd;

	fs := Coefficients(25 * (F - G) - a * Fd^2 * (y^2 + e*y + f));

	//A := AffineSpace(GF(p),7);
	//S := Scheme(A,fs);

	//Ps := RationalPoints(S);

	return fs;
end intrinsic;

intrinsic Deg15(p::RngIntElt) -> .
{}
	R<a,b,c,d,e,f,g,h,i,j,x> := PolynomialRing(Z,11);
	_<y> := PolynomialRing(R);	

	F := a * y^5 * (y-1)^5 * (y-x)^5;
	G := (y-b)^7*(y-c);

	Fds := [fac[1] : fac in Factorization(Derivative(F)*G - Derivative(G)*F) |
			Degree(fac[1]) eq 4 and fac[2] eq 1];
	assert #Fds eq 1;
	Fd := Fds[1];
	cd := LeadingCoefficient(Fd);

	fs := Coefficients(cd^2 * (F - G) - a * Fd^2 *
			(y^7 + d*y^6 + e*y^5 + f*y^4 + g*y^3 + h*y^2 + i*y + j));
	A := AffineSpace(GF(p),11);
	S := Scheme(A, fs);

	Ps := RationalPoints(S);

	return fs, Ps;
end intrinsic;

intrinsic Deg152(p::RngIntElt) -> .
{}
	R<a,b,c,d,e,f,g,h,i,j,k,l,m,n,x> := PolynomialRing(Z,15);
	_<y> := PolynomialRing(R);	

	F := a * y^5 * (y-1)^5 * (y-x)^5;
	G := (y-b)^7*(y-c);
	H := a * (y^4 + k*y^3 + l*y^2 + m*y + n)^2 * (y^7 + d*y^6 + e*y^5 + f*y^4 + g*y^3 + h*y^2 + i*y + j);

	fs := Coefficients(F - G - H);

	A := AffineSpace(GF(p),15);
	S := Scheme(A, fs);

	Ps := RationalPoints(S);

	return fs, Ps;
end intrinsic;

function trans(f);
	_<y> := Parent(f);
	return ReciprocalPolynomial(Evaluate(ReciprocalPolynomial(f),7*y));
end function;

intrinsic Deg153(p::RngIntElt) -> .
{}
	R<a,b,c,x> := PolynomialRing(Z,4);
	_<y> := PolynomialRing(R);	

	F := a * y^5 * (y-1)^5 * (y-x)^5;
	G := (y-b)^7*(y-c);

	Fds := [fac[1] : fac in Factorization(Derivative(F)*G - Derivative(G)*F) |
			Degree(fac[1]) eq 4 and fac[2] eq 1];
	assert #Fds eq 1;
	Fd := Fds[1];

	fs := Coefficients(trans(F-G) mod (trans(Fd) div 7));
	A := AffineSpace(GF(p),4);

	S := Scheme(A, fs);

	//Ps := RationalPoints(S);

	return fs;
end intrinsic;

intrinsic Deg154() -> .
{}
	R<a,b,c,x> := PolynomialRing(Q,4);
	_<y> := PolynomialRing(R);	

	F := a * y^5 * (y-1)^5 * (y-x)^5;
	G := (y-b)^7*(y-c);

	Fds := [fac[1] : fac in Factorization(Derivative(F)*G - Derivative(G)*F) |
			Degree(fac[1]) eq 4 and fac[2] eq 1];
	assert #Fds eq 1;
	Fd := Fds[1];

	fs := Coefficients((F-G) mod Fd);

	d := LCM([Denominator(r) : r in Coefficients(f), f in fs]);
	d2 := LCM([Denominator(r) : r in Coefficients(f), f in Coefficients(Fd)]);

	RZ<a,b,c,x> := PolynomialRing(Z,4);

	return [RZ!(d*f) : f in fs],PolynomialRing(RZ)!(d2*Fd);
end intrinsic;

intrinsic Deg15Solution(p::RngIntElt) -> .
{}
	fs,Fd := Deg154();
	_<a,b,c,x> := Parent(fs[1]);
	disc := Discriminant(Fd);
	fs2 := [fs[1] div (b*c)] cat fs[[2..#fs]];
	

	Rp := RSpace(GF(p),4);
	time Ps := [r : r in Rp | forall {f : f in fs2 |
		Evaluate(f,Eltseq(r)) eq 0}];
	J := Transpose(JacobianMatrix(fs2));

	good := [r : r in Ps | Dimension(Kernel(Evaluate(J,Eltseq(r)))) eq 0];

	sols := [];
	"number of good solutions", #good;
	for r in good do
		lift := HenselLift(fs2, Eltseq(r), 10)[1];
		if Evaluate(disc, Eltseq(lift)) ne 0 and
			lift[3] ne 1 and lift[3] ne lift[4] then
			Append(~sols, lift);
		end if;
	end for;

	return sols;
end intrinsic;

//F := a * y^6 * (y-1)^4 * (y-x)^2;
//G := (y-b)^3 * (y^2 + c*y + d)^2;
intrinsic Roberts2Solution(p::RngIntElt) -> .
{}
	fs := ExampleRoberts2(p);
	_<a,b,c,d,e,f,x> := Parent(fs[1]);

	Rp := RSpace(GF(p),7);
	time Ps := [r : r in Rp | forall {f : f in fs | Evaluate(f,Eltseq(r)) eq 0}];
	J := Transpose(JacobianMatrix(fs));

	good := [r : r in Ps | Dimension(Kernel(Evaluate(J,Eltseq(r)))) eq 0];

	sols := [];
	"number of good solutions", #good;
	for r in good do
		lift := HenselLift(fs, Eltseq(r), 10);
		Append(~sols,lift);
	end for;

	return sols;
end intrinsic;