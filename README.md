# etale-algebra-family

This is a package in Magma for computing isomorphism classes of local étale algebras parametrized by one variable.

More precisely, let $K$ be a number field and let $\mathfrak p$ be a finite place of $K$. Write $K_{\mathfrak p}$ for the completion of $K$ at $\mathfrak p$. Let $F\in \mathcal O_K[s,t]$ with $\deg_s(F) = 1$. Moreover, let $\mathcal A\subseteq\mathcal O_K$. This package provides an algorithm for computing the isomorphism classes of étale $\mathbb Z_3$-algebras attained by
$$K_{\mathfrak p}[t] / (F(s_0,t))$$
where $s_0$ ranges over $\mathcal A$ (and for which $F(s_0,t)$ is separable).


## Usage

To load this package in Magma, one attaches the `spec` file.

```
AttachSpec("spec");
```

Below, we give a simple example in Magma code. It computes the isomorphism classes attained by
$$\mathbb Z_3[t] / (t^3 - s_0(t-2))$$
for $s_0\in\mathbb Z_3$.

```
S<s> := PolynomialRing(Rationals());
_<t> := PolynomialRing(S);
F := t^3 - s*(t - 2);
//SetVerbose("AlgEtFam",2) //to get additional verbose information

//compute the isomorphism classes attained by Q_3[t] / (t^3 - s(t-2)) for s in Z_3
time E := EtaleAlgebraFamily(F, 3);

printf "Found %o isomorphism classes\n", #E;
printf "The 5-th one is: %o\n", SimplifyToProduct(E[5]);
```

This produces the following output.

```
Found 14 isomorphism classes
The 5-th one is: Etale algebra defined by product of [
Unramified extension defined by the polynomial x^3 + (2 + O(3^50))*x + 1 + 
O(3^50) over Unramified extension defined by a map over 3-adic field mod 3^50
] with stable neighbourhoods [
1 + 3 * OK,
756 + 2187 * OK
]
```

This shows that $\mathbb Z_3[t] / (t^3 - s_0(t-2))$ attains $14$ distinct isomorphism classes for $s_0\in\mathbb Z_3$ (for which $t^3 - s_0(t-2)$ is also separable). For instance, we have
$$\mathbb Z_3[t] / (t^3 - s_0(t-2)) \cong \mathbb Z_3[t] / (t^3 + 2t + 1)$$
if and only if $s_0\in 1 + 3\mathcal O_K$ or $s_0\in 756 + 2187\mathcal O_K$.

**example with parameter space**

More code examples can be found in [examples](examples).


## Package contents

We give a quick description of the contents of this Magma package.

* [EtaleAlgebras](EtaleAlgebras): This folder contains the main functionality for working with étale algebras and polynomials over local fields. We give a quick description for every file.
	+ [etale_algebra.m](EtaleAlgebras/etale_algebra.m): Implementation of étale algebras over a local field.
	+ [etale_algebra_family.m](EtaleAlgebras/etale_algebra_family.m): Implements the main function `EtaleAlgebraFamily`, which can compute isomorphism classes of étale algebras parametrized by a one-variable family
	+ [padic_nbhd.m](EtaleAlgebras/padic_nbhd.m): Implements p-adic parameter spaces.
	+ [separant.m](EtaleAlgebras/separant.m): Computing separants of polynomials over local fields, and other related expressions involving the roots of a polynomial over a local field.
	+ [tschirnhaus.m](EtaleAlgebras/tschirnhaus.m): Computing Tschirnhaus transformations of defining polynomials of an étale algebra over a local field.
	+ [utils.m](EtaleAlgebras/utils.m): Contains some miscellaneous functions.
* [GFE](GFE)
* [LocalFields](LocalFields)
* [examples](examples)
* [scripts](scripts)


## References

