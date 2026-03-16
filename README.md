# Formalizing Asymptotic Optimality for Convergence of Likelihood

This project formalizes classical results from likelihood estimator based the Lean theorem prover and the mathlib mathematical library.

## Main theorems
Theorem 1. (Formalized) Assumptions (1-4) in Section 3 are assumed. Then there exists an estimator sequence $\left(\hat{\theta}_n\right)_{n \geq 0}$ such that for every radius $a \in(0, \infty)$,

$$
P_{\theta_0}\left(\left|\hat{\theta}_n-\theta_0\right|<a \text { and } \ell_n^{\prime}\left(\hat{\theta}_n\right)=0\right) \rightarrow 1 \quad(n \rightarrow \infty)
$$

where $\ell_n^{\prime}\left(\hat{\theta}_n\right)$ denotes the derivative with respect to $\theta$ of the map $\theta \mapsto \rightarrow \ell_n(\theta ; \omega)$, evaluated at $\theta=\hat{\theta}_n(\omega)$.

Theorem 2. (Planned) Suppose that $X_1, \ldots, X_n$ are iid and satisfy the assumptions of Theorem 2.6, with (c) and (d) replaced by the corresponding assumptions on the third (rather than the second) derivative, that is, by the existence of a third derivative satisfying
$$
\begin{aligned}
& \left|\frac{\partial^3}{\partial \theta^3} \log f(x \mid \theta)\right| \leq M(x) \\
& \qquad \text { for all } x \in A, \quad \theta_0-c<\theta<\theta_0+c
\end{aligned}
$$
with

$$
E_{\theta_0}[M(\mathbf{X})]<\infty .
$$


Then, any consistent sequence $\hat{\theta}_n=\hat{\theta}_n\left(X_1, \ldots, X_n\right)$ of roots of the likelihood equation satisfies

$$
\sqrt{n}\left(\hat{\theta}_n-\theta\right) \xrightarrow{\mathcal{L}} N\left(0, \frac{1}{I(\theta)}\right) .
$$

## Library dependency
1. [Mathlib 4](https://github.com/leanprover-community/mathlib4)
2. [CLT](https://github.com/RemyDegenne/CLT/tree/master) for Central limit theorem
## Reference
[1] E. L. Lehmann. Theory of Point estimation. Springer, 2014.<br>
[2] CLT, https://github.com/RemyDegenne/CLT/tree/master