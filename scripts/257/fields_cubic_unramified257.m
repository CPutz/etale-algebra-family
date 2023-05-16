/*
 Number fields downloaded from the LMFDB downloaded 24 April 2023
 Below is a list called data. Each entry has the form:
   [label, polynomial, discriminant, t-number, class group]
 Here the t-number is for the Galois group
 If a class group was not computed, the entry is [-1]
To create a list L of fields, type "L := make_data();"
*/

// Cubic number fields with signature (1,1), and which are unramified outside 2, 5 and 7.

R<x> := PolynomialRing(Rationals());

data := [
<"3.1.140.1", x^3 + 2*x - 2, -140, 2, []>,
<"3.1.175.1", x^3 - x^2 + 2*x - 3, -175, 2, []>,
<"3.1.200.1", x^3 - x^2 + 2*x + 2, -200, 2, []>,
<"3.1.980.1", x^3 - x^2 + 5*x - 13, -980, 2, [3]>,
<"3.1.1960.1", x^3 - x^2 + 5*x + 15, -1960, 2, [3]>
];
function make_data() return [NumberField(r[2]) : r in data]; end function;
