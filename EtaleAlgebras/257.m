Z := Integers();

intrinsic Etale257(p::RngIntElt) -> []
{Gives the list of possible etale algebras for
signature (2,5,7) and p}
	Qp := pAdicField(p,500);
	o := O(Qp!p);

	if p eq 2 then
		D := LocalFieldDatabaseOctic2Adics();
	else
		D := LocalFieldDatabase();
	end if;
	
	B<r,a> := CreateParameterSpace(PolynomialRing(Qp,2), <0,0>, car<[Z!b+o : b in Integers(p) | b notin [0,1]]>);
	R<t> := PolynomialRing(B);
	phi1 := 4*t^5*(14 + 14*t + 20*t^2 + 25*t^3);
	phi2 := 4*t - 1;

	if p eq 2 then
		b := true; L0 := {}; L0n := {};
	else
		printf "computing etale algebras generated by phi1 - a*phi2\n";
		IndentPush();
		//b0, L0, L0n := IsomorphismClassesFamEtale(phi1 - a*phi2: D := D);
		IndentPop();
	end if;

	B<r,a> := CreateParameterSpace(PolynomialRing(Qp,2), <1,Infinity()>, car<[Z!b+o : b in Integers(p) | b ne 0]>);
	R<t> := PolynomialRing(B);
	phi1 := 4*t^5*(14 + 14*t + 20*t^2 + 25*t^3);
	phi2 := 4*t - 1;

	printf "\ncomputing etale algebras generated by phi1 - a*p^5r*phi2\n";
	IndentPush();
	b1, L1, L1n := IsomorphismClassesFamEtale(phi1 - a*r^5*phi2: D := D);
	IndentPop();

	RZ<tZ> := PolynomialRing(PolynomialRing(Integers(),2));
	printf "\ncomputing etale algebras generated by phi1 - (1+a*p^2r)*phi2\n";
	IndentPush();
	//b2, L2, L2n := IsomorphismClassesFamEtale(R!Evaluate(RZ!(phi1 - (1+a*r^2)*phi2), tZ+1): D := D);
	IndentPop();

	printf "\ncomputing etale algebras generated by p^7r*phi1 - a*phi2\n";
	IndentPush();
	//b3, L3, L3n := IsomorphismClassesFamEtale(r^7*phi1 - a*phi2: D := D);
	IndentPop();

	/*if b0 and b1 and b2 and b3 then
		printf "\nConclusive about etale algebras for p=%o\n", p;
	else
		printf "\nInconclusive about etale algebras for p=%o\n", p;
	end if;

	return [<L0,L0n>, <L1,L1n>, <L2,L2n>, <L3,L3n>];*/
	return [<L1, L1n>];
end intrinsic

intrinsic Etale257_4z() -> <>
{Gives the list of possible etale algebras for
signature (2,5,7) and p}
	p := 2;
	Qp := pAdicField(p,500);
	o := O(Qp!p);
	D := LocalFieldDatabaseOctic2Adics();
	B<r,a> := CreateParameterSpace(PolynomialRing(Qp,2), <2,Infinity()>, car<[Z!b+o : b in Integers(p) | b ne 0]>);
	R<t> := PolynomialRing(B);
	phi1 := 4*t^5*(14 + 14*t + 20*t^2 + 25*t^3);
	phi2 := 4*t - 1;

	printf "\ncomputing etale algebras generated by p^7r*phi1 - a*phi2 when 4|z\n";
	IndentPush();
	b3, L3, L3n := IsomorphismClassesFamEtale(r^7*phi1 - a*phi2: D := D);
	IndentPop();

	if b3 then
		printf "\nConclusive about etale algebras\n";
	else
		printf "\nInconclusive about etale algebras\n";
	end if;

	return <L3,L3n>;
end intrinsic

intrinsic CongrUn257(p) -> []
{}
	Qp := pAdicField(p,500);
	R<t> := PolynomialRing(Qp);
	phi1 := 4*t^5*(14 + 14*t + 20*t^2 + 25*t^3);
	phi2 := 4*t - 1;
	Phi := 25*t^3 + 20*t^2 + 14*t + 14;
	E0 := {@EtaleAlgebra(phi1 - a*phi2) : a in [2..(p-1)]@};
	E1 := {@EtaleAlgebra(Phi * (t^5 - a)) : a in [1..(p-1)]@};
	E2 := {@EtaleAlgebra(phi1 - (1 + a*p^(2*r))*phi2) : a in [1..(p-1)], r in [1..2]@};
	E3 := {@EtaleAlgebra(t * (t^7 - a)) : a in [1..(p-1)]@};

	return E0 join E1 join E2 join E3;
end intrinsic;