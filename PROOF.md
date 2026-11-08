# The supercritical log-rank law for stable matchings

## Statement

For each $n\ge 2$, take a balanced market with $n$ firms and $n$ workers. Let all firm utilities $U_{ij}$ and worker utilities $V_{ij}$ be independent and distributed as $\mathrm{Exp}(1)$, where $V_{ij}$ is worker $j$'s utility for firm $i$. The diagonal matching pairs firm $i$ with worker $i$. Write $S_n$ for the event that no $i\ne j$ satisfies both $U_{ij}>U_{ii}+\varepsilon_n$ and $V_{ij}>V_{jj}+\varepsilon_n$. Define the firms' total partner rank by
$$
R_n=\sum_{i=1}^n\sum_{j=1}^n \mathbf 1\{U_{ij}\ge U_{ii}\}.
$$
Suppose $\varepsilon_n\ge 0$, $n\varepsilon_n/\log n\to+\infty$, and $2\varepsilon_n/\log n\to\rho$ for $0\le\rho<1$. Then for every $\rho<t<1$,
$$
\Pr(R_n\le n^{1+t}\mid S_n)\longrightarrow\frac{t-\rho}{1-\rho}.
$$
In fact the proof needs only nonnegativity and $2\varepsilon_n/\log n\to\rho\in[0,1)$.

This is the proposed sharpening stated in [Formal Conjectures #7827](https://github.com/google-deepmind/formal-conjectures/issues/7827) and [PR #7828](https://github.com/google-deepmind/formal-conjectures/pull/7828). The broader question about postcritical rank estimates appears in [Pittel and Rudov, §1](https://link.springer.com/content/pdf/10.1007/s00182-026-01016-x.pdf#page=6). Their [working paper, Appendix C, Lemma 5](https://krudov.com/papers/JMP_Kirill_Rudov.pdf#page=43) gives a joint probability formula for diagonal stability and total firm rank. We derive the conditional law used here directly.

## 1. The exact integral

Set $a=e^{-\varepsilon_n}$ and $q=a^2$, so $0<q\le 1$. Both parameters may vary with $n$. Write $A_{ij}=e^{-U_{ij}}$ and $B_{ij}=e^{-V_{ij}}$. These are independent uniforms on $[0,1]$, since $\Pr(e^{-U}\le z)=\Pr(U\ge-\log z)=z$ for $0<z<1$ and $U\sim\mathrm{Exp}(1)$. Set $x_i=A_{ii}$, $y_j=B_{jj}$, $X=\sum_i x_i$, and $Y=\sum_j y_j$.

Conditional on $x,y$, a pair $i\ne j$ blocks the diagonal matching precisely when $(A_{ij},B_{ij})$ lies in the rectangle $[0,ax_i)\times[0,ay_j)$, up to null endpoints. The rectangles refer to independent pairs of coordinates. Thus the exact probability of stability given $x,y$ is
$$
K_q(x,y)=\prod_{i\ne j}(1-qx_i y_j).
$$
For any Borel set of diagonal scores, its joint probability with $S_n$ is the integral of $K_q$ over that set in the unit cube. In particular, $Z_n=\Pr(S_n)>0$ because the integrand is positive throughout the interior of the cube. The conditional law of $x,y$ has density $K_q/Z_n$.

Integrating out $y$ factorizes because each $y_j$ appears in its own group of factors:
$$
\int_{[0,1]^n}K_q(x,y)\,dy
=\prod_{j=1}^n\int_0^1\prod_{i\ne j}(1-qx_i y)\,dy.
$$

## 2. The density of the score sum on the logarithmic scale

Put $s=\sum_i x_i$ and $u_i=x_i/s$ for $s>0$. Write $\Delta_{n-1}$ for the simplex $\{u_i\ge0,\ \sum_i u_i=1\}$, using $u_1,\ldots,u_{n-1}$ as its coordinates. The Jacobian of $x=su$ in these coordinates is $s^{n-1}$. Indeed, the first $n-1$ columns of the derivative matrix are $s(e_i-e_n)$, where $e_i$ is the $i$th coordinate vector, and the last is $u$. After factoring out $s^{n-1}$, adding the first $n-1$ rows to the last gives determinant $1$.

Use $\mathbb E_\Delta$ for expectation under the uniform law on $\Delta_{n-1}$, with coordinate density $(n-1)!$. To see the density and a useful representation, apply the same change of variables to independent rate-one exponentials $E_1,\ldots,E_n$. Their joint density becomes $e^{-s}s^{n-1}$. Integrating in $s$ gives $(n-1)!$ by integration by parts, so $u=(E_i/\sum_k E_k)_i$ has this uniform law.

For $s>0$ and $su_i\le1$ for all $i$, define
$$
J_j(s,u)=\int_0^{qs}\prod_{i\ne j}(1-u_i z)\,dz.
$$
Substituting $z=qsy$ into the factor for $y_j$ gives $(qs)^{-1}J_j(s,u)$. Let
$$
W_n(s,u)=
\begin{cases}
\prod_j J_j(s,u),& su_i\le1\text{ for all }i,\\
0,&\text{otherwise},
\end{cases}
\qquad
H_n(s)=\mathbb E_\Delta W_n(s,u),
\qquad D_n=\frac{q^{-n}}{(n-1)!}.
$$
The Jacobian and the factor $(qs)^{-n}$ give the exact density formula
$$
\Pr(X\in ds,\ S_n)=D_n H_n(s)\,\frac{ds}{s},
\qquad 0<s\le n. \tag{1}
$$

### A uniform bound

On the admissible part of the simplex, $0\le u_i z\le qsu_i\le 1$ when $0\le z\le qs$. Hence $0\le J_j\le qs$ and
$$
J_j\le\int_0^{qs}e^{-(1-u_j)z}\,dz.
$$
If $s\ge 2$, then every $u_j\le1/s\le1/2$. We obtain $J_j\le(1-u_j)^{-1}$ and
$$
\prod_j(1-u_j)^{-1}
=\exp\!\bigg(\sum_j-\log(1-u_j)\bigg)\le e^2,
$$
using $-\log(1-u_j)=\int_0^{u_j}(1-v)^{-1}\,dv\le2u_j$. If $0<s<2$, the displayed integral for $J_j$ is at most $e^{qsu_j}\int_0^{qs}e^{-z}\,dz\le e^{qsu_j}$. Multiplying gives $\prod_j J_j\le e^{qs}\le e^2$. With the zero value on the inadmissible part, this proves
$$
0\le W_n(s,u)\le \min\{e^2,(qs)^n\}. \tag{2}
$$
In particular, the region $s\le 1/q$ contributes at most $D_n/n$ in (1), by integrating $(qs)^n\,ds/s$ up to $1/q$.

### The density on an interior window

Write $\rho_n=-\log q/\log n$, so $\rho_n\to\rho$. Fix $\delta>0$ with $2\delta<1-\rho$. For all sufficiently large $n$, the interval
$$
I_n=\big[n^\delta/q,\ n^{1-\delta}\big]
$$
is nonempty. We prove
$$
\sup_{s\in I_n}|H_n(s)-e^{-1}|\longrightarrow 0. \tag{3}
$$

Under the uniform simplex law, let $M=\max_i u_i$ and $Q=\sum_i u_i^2$. The exponential representation and the weak law of large numbers give $nQ\to2$ in probability, since
$$
nQ=\frac{n^{-1}\sum_i E_i^2}{(n^{-1}\sum_i E_i)^2},
\qquad \mathbb E E_i=1,\quad \mathbb E E_i^2=2.
$$
Both sample averages have finite variance. Also $\Pr(\max_i E_i>2\log n)\le n e^{-2\log n}=1/n$. On the event $\sum_i E_i\ge n/2$ and $\max_i E_i\le2\log n$, we have $M\le4\log n/n$. Consequently the simplex event $G_n=\{M\le4\log n/n\}$ has probability tending to one.

For $u\in G_n$ and $s\in I_n$, all cube constraints hold for large $n$ because $sM\le4n^{-\delta}\log n\to0$. Also $qs\ge n^\delta$. Set $L=8\log n$, which is below $qs$ for large $n$. For $0\le z\le L$ and all $j$, Taylor's formula on $0\le u_i z\le 1/2$ gives
$$
\log\prod_{i\ne j}(1-u_i z)
=-z+u_j z-\frac{Q z^2}{2}
+O(M^2 z^2+M^2 z^3).
$$
The error includes the omitted term $u_j^2z^2/2$ and the summed cubic remainder, using $\sum_i u_i^3\le M^2$. All constants here and below are independent of $j,s,u$ in this window. Since $Q\le M$ and $M\le4\log n/n$, the correction to $-z$ is $O((\log n)^3/n)$ uniformly for $z\le L$. Exponentiating and using $e^v=1+v+O(v^2)$ for $|v|\le1$ yields
$$
\prod_{i\ne j}(1-u_i z)
=e^{-z}\left[1+u_j z-\frac{Q z^2}{2}
+O\!\left(\frac{(\log n)^6}{n^2}\right)\right].
$$
On $L\le z\le qs$, the product is at most $e^{-(1-u_j)z}\le e^{-z/2}$, so its integral on that range is at most $2n^{-4}$. The tail from $L$ to infinity of the exponential times the displayed quadratic is also $O(n^{-4})$, since its absolute integrand is bounded by $C e^{-z/2}$ for an absolute constant $C$. Integration and the moments $\int_0^\infty z e^{-z}dz=1$ and $\int_0^\infty z^2 e^{-z}dz=2$ now give
$$
J_j(s,u)=1+u_j-Q+O\!\left(\frac{(\log n)^6}{n^2}\right).
$$
In particular $J_j-1=O(\log n/n)$. Expanding the logarithm of each $J_j$ and summing gives
$$
\log W_n(s,u)=\sum_j(u_j-Q)+O\!\left(\frac{(\log n)^6}{n}\right)
=1-nQ+o(1)
$$
uniformly on $s\in I_n$, $u\in G_n$. Since $nQ\to2$ in probability and $\Pr_\Delta(G_n)\to1$, for each fixed $\eta>0$ there is a simplex event of probability tending to one on which $|W_n(s,u)-e^{-1}|\le\eta$ for every $s\in I_n$. By (2), $|H_n(s)-e^{-1}|$ is at most $\eta$ plus $(e^2+e^{-1})$ times the probability of the complementary event, uniformly in $s$. Letting $\eta$ decrease to zero proves (3).

### Normalization and the score law

The logarithmic length of $I_n$ is $(1-\rho_n-2\delta)\log n$. The two pieces of $[1/q,n]$ outside $I_n$ each have logarithmic length $\delta\log n$. Therefore (1)–(3) imply
$$
(e^{-1}+o(1))(1-\rho_n-2\delta)
\le\frac{Z_n}{D_n\log n}
\le(e^{-1}+o(1))(1-\rho_n-2\delta)
   +2e^2\delta+\frac1{n\log n}.
$$
The $o(1)$ terms tend to zero for fixed $\delta$. Taking limits and then letting $\delta\downarrow0$ yields
$$
\frac{Z_n}{D_n\log n}\longrightarrow e^{-1}(1-\rho). \tag{4}
$$
For fixed $\rho<t<1$, choose $\delta$ also less than $\min(t-\rho,1-t)$, so $n^t\in I_n$ eventually. The logarithmic length from $n^\delta/q$ to $n^t$ is $(t-\rho_n-\delta)\log n$. The contribution below $n^\delta/q$ is at most $D_n(1/n+e^2\delta\log n)$. Thus the same squeeze gives
$$
\frac{\Pr(X\le n^t,\ S_n)}{D_n\log n}\longrightarrow e^{-1}(t-\rho).
$$
Dividing by (4) shows
$$
\Pr\!\left(\frac{\log X}{\log n}\le t\ \middle|\ S_n\right)
\longrightarrow \frac{t-\rho}{1-\rho}. \tag{5}
$$
For $t\le\rho$, bounding the conditional probability by its value at any $t'\in(\rho,1)$ and sending $t'\downarrow\rho$ gives zero. For $t\ge1$, it is one since $X\le n$. These statements give convergence in distribution to the uniform law on $[\rho,1]$. The same law holds for $\log Y/\log n$ because $K_q(x,y)=K_q(y,x)$ after exchanging the two indices in the product.

## 3. Transfer from scores to ranks

From (5), $X\to\infty$ and $Y/n\to0$ in conditional probability given $S_n$. In detail, for each fixed $C>0$ and each $\rho<t<1$, $C<n^t$ for large $n$, so $\limsup\Pr(X\le C\mid S_n)\le(t-\rho)/(1-\rho)$, which tends to zero as $t\downarrow\rho$. For each $\eta>0$, we have $n^t<\eta n$ for large $n$, so $\limsup\Pr(Y>\eta n\mid S_n)\le(1-t)/(1-\rho)$, which tends to zero as $t\uparrow1$.

Conditional on $x,y,S_n$, the off-diagonal pairs $(A_{ij},B_{ij})$ are independent and each is uniform on the complement of its forbidden rectangle. This follows by conditioning the product law on the intersection of the separate coordinate events. Since $a\le1$, the forbidden rectangle is contained in $\{A_{ij}\le x_i\}$. The conditional probability that $j$ is counted in firm $i$'s rank, for $i\ne j$, is consequently
$$
p_{ij}=\frac{x_i-qx_i y_j}{1-qx_i y_j}.
$$
This formula holds almost everywhere under the conditional diagonal law. The inequalities
$$
x_i(1-qy_j)\le p_{ij}\le x_i
$$
follow from $1-qx_i y_j\le1$ and $1-qy_j\le1-qx_i y_j$, respectively. The diagonal contributes $n$ to $R_n$ and the remaining terms are independent Bernoulli indicators given $x,y,S_n$. Hence their total conditional mean $\lambda=\sum_{i\ne j}p_{ij}$ and the conditional variance of $R_n$ satisfy
$$
(n-1)X-qXY\le\lambda\le(n-1)X,\qquad
\operatorname{Var}(R_n\mid x,y,S_n)\le\lambda\le nX.
$$
In particular,
$$
\left|\frac{\mathbb E(R_n\mid x,y,S_n)}{nX}-1\right|
\le\frac1X+\frac1n+\frac{qY}{n}.
$$
The right side tends to zero in conditional probability since $q\le1$. On $X\ge1$, conditional Chebyshev bounds the probability that $R_n/(nX)$ differs from its conditional mean by more than any fixed $\eta>0$ by $1/(\eta^2 nX)\le1/(\eta^2 n)$. Averaging over $x,y$ and using $\Pr(X<1\mid S_n)\to0$ proves $R_n/(nX)\to1$ in conditional probability.

Taking logarithms gives
$$
\frac{\log(R_n/n)}{\log n}-\frac{\log X}{\log n}
=\frac{\log(R_n/(nX))}{\log n}\longrightarrow0
$$
in conditional probability. For $\rho<t<1$, choose $\eta>0$ with $t-\eta,t+\eta\in(\rho,1)$. Outside an event of conditional probability tending to zero, the two logarithmic variables differ by at most $\eta$. The conditional probability that the rank variable is at most $t$ is therefore squeezed between the score CDF at $t-\eta$ minus $o(1)$ and that at $t+\eta$ plus $o(1)$. By (5), sending $\eta\downarrow0$ gives the claimed limit. The event for the rank variable is exactly $R_n\le n^{1+t}$ because $\log n>0$. $\square$
