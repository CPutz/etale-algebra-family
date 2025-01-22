# etale-algebra-family

This is a package in Magma for computing isomorphism classes of local étale algebras parametrized by one variable. This package accompanies the PhD thesis \[1\].

For a more precise description, let $K$ be a number field and let $\mathfrak p$ be a finite place of $K$. Write $K_{\mathfrak p}$ for the completion of $K$ at $\mathfrak p$. Let $F\in \mathcal O_K[s,t]$ with $\deg_s(F) = 1$. Moreover, let $\mathcal A\subseteq\mathcal O_K$. This package provides an algorithm for computing the isomorphism classes of étale $K_{\mathfrak p}$-algebras attained by
$$K_{\mathfrak p}[t] / (F(s_0,t))$$
where $s_0$ ranges over $\mathcal A$ (and for which $F(s_0,t)$ is separable).


## Usage

This package is compatible with Magma `V2.28-8`. To load the package in Magma, one attaches the `spec` file.

```
AttachSpec("spec");
```

Below, we give a simple example in Magma code. It computes the isomorphism classes attained by
$$\mathbb Q_3[t] / (t^3 - s_0(t-2))$$
for $s_0\in\mathbb Z_3$.

```
S<s> := PolynomialRing(Rationals());
_<t> := PolynomialRing(S);
F := t^3 - s*(t - 2);
//SetVerbose("AlgEtFam",2) //to get additional verbose information

//compute the isomorphism classes attained by Q_3[t] / (t^3 - s(t-2)) for s in Z_3
time E := EtaleAlgebraFamily(F, 3);

printf "Found %o isomorphism classes\n", #E;
printf "The 12-th one is: %o\n", SimplifyToProduct(E[12]);
```

This produces the following output.

```
Found 14 isomorphism classes
The 12-th one is: Etale algebra defined by product of [
Unramified extension defined by the polynomial x + 2 + O(3^50) over 
Unramified extension defined by a map over 3-adic field mod 3^50,
Totally ramified extension defined by the polynomial x^2 - 3 + O(3^50) over 
Unramified extension defined by a map over 3-adic field mod 3^50
] with stable neighbourhoods [
27 + 1594323 * (OK^2 - {0}),
54 + 243 * OK,
2214 + 6561 * OK,
19710 + 59049 * OK
]
```

This output above shows that $\mathbb Q_3[t] / (t^3 - s_0(t-2))$ attains $14$ distinct isomorphism classes for $s_0\in\mathbb Z_3$ (for which $t^3 - s_0(t-2)$ is also separable). For instance, we have
$$\mathbb Q_3[t] / (t^3 - s_0(t-2)) \cong \mathbb Q_3(\sqrt{3}) \times \mathbb Q_3$$
with $s_0\in\mathbb Z_3$ if and only if $s_0\in 2\cdot 3^3 + 3^5\mathbb Z_3$ or $`s_0\in 3^3 + 3^7(\mathbb Z_3^2\setminus \{0\})`$.

More examples can be found in [examples](https://github.com/CPutz/etale-algebra-family/tree/master/examples).


## Contents

We give a quick description of the contents of this Magma package.

* [EtaleAlgebras](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras): This folder contains the main functionality for working with étale algebras and polynomials over local fields. We give a quick description for every file.
	+ [etale_algebra.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/etale_algebra.m): Implementation of étale algebras over a local field.
	+ [etale_algebra_family.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/etale_algebra_family.m): Implements the main function `EtaleAlgebraFamily`, which can compute isomorphism classes of étale algebras parametrized by a one-variable family
	+ [padic_nbhd.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/padic_nbhd.m): Implements $p$-adic parameter spaces.
	+ [separant.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/separant.m): Computing separants of polynomials over local fields, and other related expressions involving the roots of a polynomial over a local field.
	+ [tschirnhaus.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/tschirnhaus.m): Computing Tschirnhaus transformations of defining polynomials of an étale algebra over a local field.
	+ [utils.m](https://github.com/CPutz/etale-algebra-family/tree/master/EtaleAlgebras/utils.m): Contains some miscellaneous functions.
* [GFE](https://github.com/CPutz/etale-algebra-family/tree/master/GFE): This folder contains functions for computing étale algebras arising from Belyi maps and generalized Fermat equations of various signatures. See \[1\] for 
	+ [257.m](https://github.com/CPutz/etale-algebra-family/tree/master/GFE/257.m): Functions for the degree $8$ Belyi map corresponding to the generalized Fermat equation of signature $(2,5,7)$ (or permutations thereof).
	+ [257_relative.m](https://github.com/CPutz/etale-algebra-family/tree/master/GFE/257_relative.m): Functions for the degree $7$ Belyi map (over $\mathbb{Q} {(}\sqrt{21}{)}$) corresponding to the generalized Fermat equation of signature $(2,5,7)$ (or permutations thereof).
	+ [3511.m](https://github.com/CPutz/etale-algebra-family/tree/master/GFE/3511.m): Functions for the degree $11$ Belyi map corresponding to the generalized Fermat equation of signature $(3,5,11)$ (or permutations thereof).
	+ [357.m](https://github.com/CPutz/etale-algebra-family/tree/master/GFE/357.m): Functions for the degree $7$ Belyi map corresponding to the generalized Fermat equation of signature $(3,5,7)$ (or permutations thereof).
* [LocalFields](https://github.com/CPutz/etale-algebra-family/tree/master/LocalFields): Contains some useful functionality for finite extensions of $p$-adic fields.
	+ [local_field_database.m](https://github.com/CPutz/etale-algebra-family/tree/master/LocalFields/local_field_database.m): Implements a data structure for pre-computed databases of $p$-adic fields. In particular, it contains LMFDB data for degree $8$ extensions of $\mathbb Q_2$ and degree $10$ extensions of $\mathbb Q_5$.
	+ [subfields.m](https://github.com/CPutz/etale-algebra-family/tree/master/LocalFields/subfields.m): Functions for computing the subfields of a $p$-adic field.
* [examples](https://github.com/CPutz/etale-algebra-family/tree/master/examples): This folder contains some code examples using this package.
* [scripts](https://github.com/CPutz/etale-algebra-family/tree/master/scripts): This folder contains various Magma scripts used for the computations in \[1\].


## References

\[1\] Casper Putz. \`Enumeration of local and global étale algebras applied to generalized Fermat equations\`. PhD thesis. Vrije universiteit Amsterdam, 2024. [https://research.vu.nl/en/publications/enumeration-of-local-and-global-étale-algebras-applied-to-general](https://research.vu.nl/en/publications/enumeration-of-local-and-global-%C3%A9tale-algebras-applied-to-general)

