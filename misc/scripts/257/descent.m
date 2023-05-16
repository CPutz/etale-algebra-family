
printf "\n==================================================================\n";
printf "We perform the computations from Proposition ?.\n";
printf "==================================================================\n\n";

R<t> := PolynomialRing(Rationals());
L := NumberField(t^7 - 5);
OL := Integers(L);

_<x> := PolynomialRing(L);

S,m := pSelmerGroup(2,Support(5*OL));

sol := [];
for s in S do
	u := s@@m;
	H := HyperellipticCurve(u * (u^2 * x^4 - 154*u * x^2 + 6125));
	if forall { p : p in Support(2*OL) |
			IsLocallySoluble(H,p) } then
		Append(~sol, s);
	end if;
end for;

assert #sol eq 2;
assert sol[1] eq m(1);
assert sol[2] eq m(5);

printf "The class of x^2 - 154x + 6125 is equal to 1 or 5 mod (L^*)^2.\n";
printf "\ndone\n";