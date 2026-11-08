# Conditional logarithmic partner ranks

This repository gives a Lean proof of a proposed log-rank law for random matching
markets with switching costs. It proves the conjecture stated in
[Formal Conjectures issue #7827](https://github.com/google-deepmind/formal-conjectures/issues/7827)
and a stronger version that removes one of its assumptions. The package also
proves exact probability identities, score limits, and estimates that connect
scores to partner ranks.

The result describes a **fixed matching conditioned on being stable**. This
conditioning matters: it changes the distribution of markets. Below we state the
model, the original conjecture, the stronger theorem, and the other results in the
package.

## Model and ranks

For each integer $`n\ge2`$, there are $`n`$ firms and $`n`$ workers. All $`2n^2`$ utilities
are independent rate-one exponential random variables. Write $`U_{ij}`$ for firm
$`i`$'s utility from worker $`j`$, and $`V_{ij}`$ for worker $`j`$'s utility from firm $`i`$.
Higher utility is better.

Fix the diagonal matching: firm $`i`$ is assigned worker $`i`$. At a common switching
cost $`\varepsilon_n\ge0`$, a pair would leave its assigned partners only if **both**
agents gain strictly more than $`\varepsilon_n`$. Thus the stability event $`S_n`$ is
that no $`i\ne j`$ satisfies both inequalities

```math
U_{ij}\gt U_{ii}+\varepsilon_n,\qquad
V_{ij}\gt V_{jj}+\varepsilon_n.
```

A firm's partner rank is one plus the number of workers it prefers to its assigned
worker; rank 1 is best. Define the total firm partner rank by

```math
R_n=\sum_{i,j=1}^n\mathbf{1}_{U_{ij}\ge U_{ii}}.
```

Here $`\mathbf{1}`$ denotes an indicator. The assigned worker contributes one, and
ties have probability zero. Consequently $`R_n/n`$ is the firms' average partner
rank, between 1 and $`n`$.

## Original conjecture, proved here

The precise conjecture in [#7827](https://github.com/google-deepmind/formal-conjectures/issues/7827)
is the following. For every nonnegative cost sequence and every $`\rho\in[0,1)`$,
assume

```math
\frac{n\varepsilon_n}{\log n}\longrightarrow+\infty,
\qquad
\frac{2\varepsilon_n}{\log n}\longrightarrow\rho.
```

Then, for each real $`t`$ with $`\rho\lt t\lt 1`$,

```math
\Pr\!\left(R_n/n\le n^t\mid S_n\right)
\longrightarrow\frac{t-\rho}{1-\rho}.
```

The first assumption specifies the *supercritical* cost regime:
$`\varepsilon_n`$ is asymptotically larger than $`(\log n)/n`$. The second specifies
its logarithmic scale. Equivalently, the logarithmic rank variable
$`L_n=\log(R_n/n)/\log n`$ converges in distribution to the uniform law on
$`[\rho,1]`$.

This package proves that conjecture. Its conditional sampling scheme differs
from the market-first question discussed below.

## Stronger theorem

**The supercritical lower bound is unnecessary.** Nonnegativity and
$`2\varepsilon_n/\log n\to\rho\in[0,1)`$ alone imply the same conditional rank
limit. In particular, the result covers zero costs, fixed nonnegative costs, and
vanishing costs of any rate, all with $`\rho=0`$.

For example, when $`\rho=0`$, the conditional probability that firms' average
partner rank is at most $`n^{1/4}`$ tends to $`1/4`$. More generally, a cutoff $`n^t`$
with $`0\lt t\lt 1`$ has limiting probability $`t`$.

The main declarations are
[`ConditionalLogRank.logRankLaw`](Solution.lean) and
[`ConditionalLogRank.supercriticalLogRankLaw`](Solution.lean). The latter retains
both assumptions of the original conjecture. Lean indexes market sizes by
$`n=k+2`$, so it covers every $`n\ge2`$ without the exceptional values of $`\log n`$ at
sizes zero and one. The statements quantify over every interior cutoff
$`\rho\lt t\lt 1`$. No monotonicity assumption or rate of convergence is imposed. The
usual distributional formulation follows from these interior CDF limits; it is
not a separate exported weak-convergence declaration.

## Which distribution does this describe?

Draw a random market, fix the diagonal matching, and keep the draw only when that
matching is stable. The theorem describes ranks among these retained draws.

This differs from drawing a market once and then selecting uniformly from its
stable matchings. For this rank statistic, symmetry gives an equivalent
experiment: weight markets in proportion to their number of stable matchings,
then choose a stable matching uniformly within the selected market. Markets with
more stable matchings receive more weight in that experiment. The probability
limits proved here are
for the conditional law defined above. They do not establish the corresponding
limit for an ordinary random market followed by a uniform stable choice.

## Other results in the package

The following are part of the proof library, beyond the statement in #7827.
Throughout this section, probabilities conditioned on $`S_n`$ use the same fixed
matching as above. Set

```math
x_i=e^{-U_{ii}},\qquad y_j=e^{-V_{jj}},\qquad
X_n=\sum_i x_i,\qquad Y_n=\sum_j y_j,\qquad
q_n=e^{-2\varepsilon_n}.
```

These transformed utilities are called *scores* in the Lean files. A smaller
score means a larger utility. They are auxiliary variables, not ordinal ranks or
utilities averaged across agents.

### Finite-market identities and positivity

For every finite size $`n`$, including zero and one, and every nonnegative cost,
$`\Pr(S_n)\gt 0`$. Thus conditioning is well-defined. This is
[`ConditionalLogRank.stability_probability_pos`](Solution.lean); the library also
proves measurability of stability and rank events and that the conditional measure
is a probability measure. See [MarketBasics.lean](SupercriticalLogRank/MarketBasics.lean).

The exponential-to-score transform gives independent uniforms on $`[0,1]`$ before
conditioning. For a fixed cost, write $`q=e^{-2\varepsilon}`$. Given diagonal
scores $`x,y`$, the probability that the diagonal matching is stable is

```math
K_q(x,y)=\prod_{i\ne j}(1-qx_i y_j).
```

Consequently, the joint probability of stability and any measurable event in the
diagonal scores is the integral of $`K_q`$ over that event in the unit cube. The
conditional diagonal-score density is $`K_q/\Pr(S_n)`$. Integrating out workers'
scores factorizes into one-dimensional column integrals. Firm and worker score
sums have exactly the same conditional distribution at every finite size. See
[ConditionalIntegral.lean](SupercriticalLogRank/ConditionalIntegral.lean) and
[ColumnFactorization.lean](SupercriticalLogRank/ColumnFactorization.lean).

### Exact radial identity and normalization

For $`n\ge1`$, let $`u`$ be uniform on the simplex $`u_i\ge0`$, $`\sum_i u_i=1`$. For
$`s\gt 0`$, define

```math
J_j(s,u)=\int_0^{qs}\prod_{i\ne j}(1-u_i z)\,dz,\qquad
W_n(s,u)=\mathbf{1}_{\forall i,\,su_i\le1}\prod_j J_j(s,u),\qquad
H_{n,q}(s)=\mathbb E_u[W_n(s,u)].
```

The radial identity, stated in Lean as an equality of cutoff integrals, is

```math
\Pr(X_n\le c,\ S_n)
=\frac{q^{-n}}{(n-1)!}\int_0^c H_{n,q}(s)\,\frac{ds}{s}
\qquad(c\ge0).
```

The package proves the simplex change of variables and its normalization, the
uniform bound

```math
0\le H_{n,q}(s)\le\min\!\left(e^2,(qs)^n\right)
\qquad(0\lt q\le1,\ s\gt 0),
```

and convergence $`H_{n,q_n}(s)\to e^{-1}`$ uniformly on every interior window
$`n^\delta/q_n\le s\le n^{1-\delta}`$, for fixed $`\delta\gt 0`$. Under the logarithmic
scale assumption, these windows are nonempty eventually whenever
$`2\delta\lt 1-\rho`$.

Under the same logarithmic-scale assumption, the general mass-limit theorem
gives, for $`\rho\le t\le1`$,

```math
\frac1{\log n}\int_0^{n^t} H_{n,q_n}(s)\,\frac{ds}{s}
\longrightarrow e^{-1}(t-\rho).
```

In particular, combining this with the exact radial identity gives the stability
normalization

```math
\frac{\Pr(S_n)}{\bigl(q_n^{-n}/(n-1)!\bigr)\log n}
\longrightarrow e^{-1}(1-\rho).
```

The last formula is a consequence of the proved identity and general mass-limit
lemma; it is not exported as a separate market-probability theorem. The relevant
sources are [Radial.lean](SupercriticalLogRank/Radial.lean),
[ExactRadial.lean](SupercriticalLogRank/ExactRadial.lean),
[GlobalBound.lean](SupercriticalLogRank/GlobalBound.lean),
[InteriorLimit.lean](SupercriticalLogRank/InteriorLimit.lean), and
[RadialLimit.lean](SupercriticalLogRank/RadialLimit.lean).

### Conditional score laws and transfer to ranks

Under the stronger theorem's assumptions, for each $`\rho\lt t\lt 1`$,

```math
\Pr(X_n\le n^t\mid S_n)\longrightarrow\frac{t-\rho}{1-\rho},
\qquad
\Pr(Y_n\le n^t\mid S_n)\longrightarrow\frac{t-\rho}{1-\rho}.
```

These are the two marginal score laws in
[ScoreLimit.lean](SupercriticalLogRank/ScoreLimit.lean). They do not assert a joint
limit or independence. General consequences in
[ScoreConsequences.lean](SupercriticalLogRank/ScoreConsequences.lean) imply that
$`X_n,Y_n\to\infty`$ and $`X_n/n,Y_n/n\to0`$ in conditional probability.

Given the diagonal scores and stability, off-diagonal pairs remain independent.
For $`i\ne j`$, the conditional probability that worker $`j`$ contributes to firm
$`i`$'s rank is, almost surely,

```math
p_{ij}=\frac{x_i-qx_i y_j}{1-qx_i y_j},
\qquad x_i(1-qy_j)\le p_{ij}\le x_i.
```

The package proves this formula, variance and Chebyshev bounds for the resulting
rank counts, and a bound that transfers estimates at fixed diagonal scores to
the conditioned market. Combining them with the score tails proves

```math
\frac{R_n}{nX_n}\longrightarrow1
\quad\text{in probability conditional on }S_n.
```

Here the ratio statement specializes a general concentration theorem whose
hypotheses are the two score-tail limits. The package also proves general lemmas
transferring the score CDF to ranks through this
ratio estimate and a logarithmic perturbation. See
[RankTransfer.lean](SupercriticalLogRank/RankTransfer.lean),
[FiberBound.lean](SupercriticalLogRank/FiberBound.lean),
[LogVariables.lean](SupercriticalLogRank/LogVariables.lean), and
[Assembly.lean](SupercriticalLogRank/Assembly.lean). The complete rank law is
assembled in [Theorem.lean](SupercriticalLogRank/Theorem.lean).

### Auxiliary estimates and definitions

The remaining modules supply the estimates used above:

| Modules | Contents |
| --- | --- |
| [Model](SupercriticalLogRank/Model.lean) | Market, ranks, conditioning, score kernel, simplex law, and radial-density definitions. |
| [SimplexConcentration](SupercriticalLogRank/SimplexConcentration.lean) | Exponential moments $`\mathbb E[E^k]=k!`$, exponential maximum bounds, the normalized-exponential representation of the simplex law, $`n\sum_i u_i^2\to2`$ in probability, and a bound $`\max_i u_i\le4\log n/n`$ with probability tending to one. |
| [Taylor](SupercriticalLogRank/Taylor.lean) | Explicit logarithm and exponential remainder bounds, column-integral approximations, and product estimates for the radial weight. |
| [Scales](SupercriticalLogRank/Scales.lean) | Vanishing error estimates and the growth comparisons needed on the interior windows. |
| [RadialMeasurability](SupercriticalLogRank/RadialMeasurability.lean) | Measurability of column integrals, radial weights, and radial densities. |

[PROOF.md](PROOF.md) gives the mathematical argument in ordinary notation. The
links above cover every proof module; the library also contains the technical
lemmas needed to justify these identities and limits.

## Relationship to the literature

[Pittel and Rudov (2026)](https://doi.org/10.1007/s00182-026-01016-x) supply the
exponential-utility switching-cost model and ask about ranks under a uniform
stable choice in a realized market. Appendix C, Lemma 5 of their
[December 2024 working paper](https://krudov.com/papers/JMP_Kirill_Rudov.pdf)
gives a joint stability/rank probability formula for a fixed matching. This
package derives its conditional integral directly in Lean.

The conditional limit in #7827 and the stronger theorem here concern a different
sampling scheme from the published market-first rank question. This distinction
is essential to the interpretation.

The balanced model and finite conditioning definitions were adapted from
[Formal Conjectures PR #7828](https://github.com/google-deepmind/formal-conjectures/pull/7828)
under Apache-2.0. The substantive proof is contained in this standalone
repository. No changes to that statement contribution are part of this package.

## Lean files and verification

Lean and Mathlib are pinned to **4.35.0**, with exact dependency revisions in
[lake-manifest.json](lake-manifest.json). Run:

```sh
lake exe cache get
lake --wfail build SupercriticalLogRank Solution
lake build Challenge
python3 scripts/audit.py
```

[Challenge.lean](Challenge.lean) independently defines the model and states three
declarations: positivity, the general rank law, and its supercritical special
case. Its three deliberate `sorry` placeholders are the statement side of
Palomar's Comparator format. [Solution.lean](Solution.lean) repeats those
definitions and proves the same declarations using the proof library; it does not
import Challenge. [comparator.json](comparator.json) selects these three
statements for comparison. The supporting results described above are also Lean
proofs, although they are not separate Comparator selections.

The proof build must have no warnings. The Challenge build emits the three
expected placeholder warnings. [scripts/audit.py](scripts/audit.py) checks for
proof-source holes and collects transitive axioms for imported declarations in
both project namespaces. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. [audit/STATEMENT_AUDIT.md](audit/STATEMENT_AUDIT.md) records the statement
checks and verification scope.

The GitHub workflow runs Palomar's pinned mechanical preflight, including
Comparator and independent kernel checks. Its report applies to the exact source
commit checked. Mechanical verification does not establish novelty or replace
expert mathematical review.

Codex helped formalize the results in Lean and assisted with statement checks,
axiom audits, toolchain porting, and package preparation.
[formalization.yaml](formalization.yaml) records sources, maintenance, automation,
and review status. No independent human mathematical review is claimed.
