intrinsic ComputeInvariants(C::RngMPol, L::SeqEnum) -> SeqEnum
{}
	S := PolynomialRing(C);
	f := S!Reverse([1] cat [C.i : i in [1..Rank(C)]]);
	df := Derivative(f);
	I := [];
	for l in L do
		l;
		time Append(~I, <l, Subresultant(df^l[2], f^l[1], l[3])>);
	end for;
	return I;
end intrinsic;

intrinsic ComputeInvariants0(C::RngMPol, L::SeqEnum) -> SeqEnum
{}
	S := PolynomialRing(C);
	f := S!Reverse([1, 0] cat [C.i : i in [1..Rank(C)]]);
	df := Derivative(f);
	I := [];
	for l in L do
		l;
		time Append(~I, <l, Subresultant(df^l[2], f^l[1], l[3])>);
	end for;
	return I;
end intrinsic;

intrinsic SaveInvariants(f::MonStgElt, I::SeqEnum)
{}
	SetColumns(0);
	for i in I do
        Write(f, Sprintf("%o: %o,", i[1], i[2]));
    end for;
end intrinsic;