AttachSpec("spec");
K := QuadraticField(21);
SetVerbose("EtaleAlg",true);

for p in [2,3,5,7,11] do
	for P in Decomposition(K,p) do
		printf "computing etale algebras for prime above %o", p;
		time EtaleAlgebras257Relative(P[1]);
	end for;
end for;