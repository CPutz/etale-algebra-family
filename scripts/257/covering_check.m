// Load this file from the main folder

load "misc/scripts/257/covering.m";
_<X> := PolynomialRing(Rationals());

printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

psi := CsigmatoE;
pi := CtoCsigma;

Bpsi := BaseScheme(psi);
Bpi := BaseScheme(pi);

Bpsi_pts,Lpsi := PointsOverSplittingField(Bpsi);
Bpi_pts,Lpi := PointsOverSplittingField(Bpi);

// pi is defined everywhere
assert #Bpi_pts eq 0;

for P in Bpsi_pts do
	B := Pullback(pi, P);
	pts,LP := PointsOverSplittingField(B);
	for p in pts do
		// we only consider the affine points of C
		if p[3] ne 0 then
			assert p eq C![0,0,1] or Phi(p) eq P1![1,1];
		end if;
	end for;
end for;

printf "psi ⚬ pi is only undefined for (0,0) and points (s,t) with Phi(s,t) = 1.\n";

G,GtoE := MordellWeilGroup(E);
EQ := [GtoE(g) : g in G];
printf "The Mordell-Weil group of E/Q is given by %o\n", EQ;

B := BaseScheme(pi * psi);
for P in EQ do
	C := Cluster(E,P);
	pts,LP := PointsOverSplittingField(Pullback(pi * psi, C));
	good_pts := [p : p in pts | p notin B and p[3] ne 0];

	for p in good_pts do
		assert
			Evaluate(X^2 - 7/20*X + 7/80, p[1] / p[3]) eq 0 and
			Evaluate(X^2 - 7/20*X + 7/80, p[2] / p[3]) eq 0; 
	end for;
end for;

printf "The points of E(Q) lift to (affine) C(L) only if L contain Q(sqrt{-91}).\n";

printf "\ndone\n";