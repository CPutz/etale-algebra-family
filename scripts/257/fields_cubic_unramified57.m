/*
 Number fields downloaded from the LMFDB downloaded 25 April 2023
 Below is a list called data. Each entry has the form:
   [label, polynomial, discriminant, t-number, class group]
 Here the t-number is for the Galois group
 If a class group was not computed, the entry is [-1]
To create a list L of fields, type "L := make_data();"
*/

// Cubic number fields unramified outside 5 and 7.

R<x> := PolynomialRing(Rationals());

data := [
<"3.3.49.1", x^3 - x^2 - 2*x + 1, 49, 1, []>,
<"3.1.175.1", x^3 - x^2 + 2*x - 3, -175, 2, []>
];
function make_data() return [NumberField(r[2]) : r in data]; end function;
