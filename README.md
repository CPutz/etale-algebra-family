# etale-algebra-family

This is a package in Magma for computing isomorphism classes of local étale algebras parametrized by one variable.

More precisely, let $K$ be a number field and let $\mathfrak p$ be a finite place of $K$. Write $K_{\mathfrak p}$ for the completion of $K$ at $\mathfrak p$. Let $F\in \mathcal O_K[s,t]$ with $\deg_s(F) = 1$. Moreover, let $\mathcal A\subseteq\mathcal O_K$. This package provides an algorithm for computing the isomorphism classes attained by
$$K_{\mathfrak p}[t] / (F(s_0,t))$$
where $s_0$ ranges over $\mathcal A$.

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
#E;
```

More code examples can be found in [examples](examples).

## References

