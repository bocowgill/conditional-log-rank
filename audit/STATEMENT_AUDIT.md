# Statement audit

Date: November 8, 2026. Evidence basis: agent self-review and Lean checking.
Codex helped formalize the results in Lean and assisted with this statement and
axiom audit. No independent human mathematical review is claimed.

## Selected mathematical content

The three selected declarations are `ConditionalLogRank.logRankLaw`,
`ConditionalLogRank.supercriticalLogRankLaw`, and
`ConditionalLogRank.stability_probability_pos`. The first is the principal
asymptotic theorem. The second is its special case. The third verifies that
the conditional probability uses a nonzero denominator.

## Definitions and quantifiers

- `Profile n` has one real coordinate for each element of
  `Bool × Fin n × Fin n`, hence exactly two directed utility arrays.
- `marketMeasure n` is the product of `expMeasure 1` over all coordinates.
  These are independent rate-one exponentials, rather than random ranks or
  a law conditioned on the market's total stable count.
- Side `false` gives firm i's utility for worker j; side `true` gives worker j's
  utility for firm i. The diagonal assigns i to i.
- `stableEvent` excludes every i != j for which both utility gains strictly
  exceed epsilon. The worker's comparison is V_ij against V_jj, not V_ii.
- `firmRankSum` counts utilities at least the assigned utility. The assigned
  coordinate contributes one. Under the continuous product law there are
  almost surely no ties.
- The cutoff R <= n^(1+t) concerns the TOTAL firm rank R, equivalently average
  rank at most n^t for the positive sizes in the limit.
- `conditionalRankProbability` is P(stable and cutoff)/P(stable). The positivity
  theorem proves P(stable)>0 for all nonnegative costs and finite n.
- The cost sequence is nonnegative for every n >= 2. Its values at n=0,1 do
  not enter the limit. No monotonicity, vanishing-cost, or count-concentration
  premise is added.
- The scale parameter satisfies 0 <= rho < 1. The test cutoff satisfies
  rho < t < 1. Thus the denominator 1-rho is positive. Endpoint CDF values
  and convergence rates are not among the selected statements.
- The sequence n=k+2 runs through every size >= 2. It is not a sparse
  subsequence.
- The supercritical special case adds n epsilon_n/log n -> infinity.
  The general theorem's proof does not need that premise.
- Empty and singleton markets have probability-one stability; their ranks
  do not affect the asymptotic statement.

## Source fidelity

Pittel and Rudov supply the utility model and broader open rank questions.
The published Section 3 question concerns a uniform stable lottery in a realized
market; this theorem does not answer it. Their published paper and December 2024
working paper are background sources,
not sources to which the exact conditional CDF limit is attributed. The precise
claim is stated in issue 7827 and is proved by this standalone development.
Literature novelty and priority remain unverified. Source-author endorsement
has not been requested.

The definitions adapted from Formal Conjectures PR 7828 retain its Apache-2.0
credit. This submission contains its substantive proof. It leaves the original
PR and its placeholder proof unchanged. Its probability law conditions a fixed
matching on stability; it does not determine ranks under a uniform stable choice
in an ordinary random market.

## Proof and statement separation

Challenge imports Mathlib alone and explicitly states all market definitions.
Solution repeats those definitions and proves the selected statements using
SupercriticalLogRank. It does not import Challenge. The selected Solution
proofs compile without additional hypotheses. Comparator must independently
confirm that these have exactly the advertised Challenge types.

## Toolchain port

The original package used Lean/Mathlib 4.33.1. The isolated submission uses
4.35.0, supported by Palomar. All proof-source modules now use the module
system with public imports and exposed public declarations. The mathematical
statements and hypotheses of the original named theorems were preserved.
Changes inside proofs replace renamed product inequalities, measurable-function
and probability-map APIs, null-measurability arguments, and deprecated tactic
steps. No axioms or unproved assumptions were introduced.

`original-source-sha256.json` pins the original 21 Lean sources before the
port. The original package is preserved separately.

## Verification boundary

The proof-only warning-as-error build and the Challenge build are distinct.
Challenge deliberately has three placeholder proofs; Solution and the proof
library must contain none. The source scanner has positive controls. The
axiom audit collects transitive axiom dependencies from Lean's environment
for all public declarations in both project namespaces. Only propext,
Classical.choice, and Quot.sound are permitted.

The Palomar full mechanical workflow is an additional gate, including
Comparator and independent kernels. An ordinary build or source scan is not
represented as that gate. A passing mechanical report is not human peer review
or certification of mathematical novelty.
