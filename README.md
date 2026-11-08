# Conditional logarithmic partner ranks

A standalone Lean proof for a balanced random matching market with switching costs.
This repository is separate from Formal Conjectures and from the paused market-first
research campaign.

For each n >= 2, let all firm utilities U_ij and worker utilities V_ij be independent
rate-one exponentials. Worker j's utility for firm i is V_ij. The fixed diagonal
matching pairs i with i. It is stable at cost epsilon_n when no i != j satisfies both

\[
U_{ij}>U_{ii}+\varepsilon_n,\qquad V_{ij}>V_{jj}+\varepsilon_n.
\]

Let S_n be this stability event, and let

\[
R_n=\sum_{i,j=1}^n\mathbf 1\{U_{ij}\ge U_{ii}\}.
\]

The assigned partner contributes one to each firm's rank. Utilities have no ties
almost surely. Thus R_n/n is the average one-based firm partner rank.

If epsilon_n >= 0 and

\[
\frac{2\varepsilon_n}{\log n}\longrightarrow\rho\in[0,1),
\]

then, for every rho < t < 1,

\[
\Pr(R_n\le n^{1+t}\mid S_n)\longrightarrow\frac{t-\rho}{1-\rho}.
\]

`ConditionalLogRank.logRankLaw` proves this limit along n=k+2. The cost values at
n=0 and n=1 are immaterial. There is no monotonicity assumption. The selected limit
statements do not assert endpoint cutoffs or rates of convergence.

`ConditionalLogRank.supercriticalLogRankLaw` is the same result with the additional
hypothesis n epsilon_n/log n -> infinity. That hypothesis is unnecessary for the
more general theorem. `ConditionalLogRank.stability_probability_pos` proves that
the conditioning event has strictly positive probability at every finite size and
nonnegative cost, including sizes zero and one.

The probability conditions a fixed matching on stability. Drawing a market first
and then drawing uniformly from its stable matchings gives a different law. This
repository does not prove that market-first law, any of the six market-first
conjectures, or the later stable-count separation theorem.

## Source relationship

[Pittel and Rudov (2026)](https://doi.org/10.1007/s00182-026-01016-x) supply the
exponential-utility switching-cost model and ask broader partner-rank questions.
Appendix C, Lemma 5 of their [December 2024 working paper](https://krudov.com/papers/JMP_Kirill_Rudov.pdf)
gives a joint stability/rank probability formula. The precise conditional CDF limit
above is our proposed sharpening and proof; it is not attributed to them. No author
endorsement or literature-priority certification is claimed.

The balanced model and finite conditioning definitions were adapted from
[Formal Conjectures PR 7828](https://github.com/google-deepmind/formal-conjectures/pull/7828),
under Apache-2.0. The original PR and its placeholder proof are unchanged.
This repository contains the complete substantive proof, rather than a wrapper
around a separately hosted proof.

## Statement and proof

- `Challenge.lean` gives independent, explicit market definitions and the three
  advertised declarations. Its three deliberate `sorry` placeholders are part of
  the Comparator statement format.
- `Solution.lean` repeats those definitions and proves the same three declarations
  using `SupercriticalLogRank/`. It does not import Challenge.
- `comparator.json` selects the three declarations for independent comparison.
- `SupercriticalLogRank/` contains the conditional integral, radial change of
  variables, simplex concentration, normalization, and rank-transfer proofs.
- `PROOF.md` gives the informal argument. `audit/STATEMENT_AUDIT.md` records the
  statement review and the boundaries of the verification claims.
- `formalization.yaml` records sources, human responsibility, AI contributions,
  and review status. The proof and packaging were produced by Codex agents under
  Bo Cowgill's direction. No independent human mathematical review is claimed.

## Verification

Lean and Mathlib are pinned to 4.35.0, with exact dependency revisions in the
committed manifest. Run:

```sh
lake exe cache get
lake --wfail build SupercriticalLogRank Solution
lake build Challenge
python3 scripts/audit.py
```

The proof build must have no warnings. The Challenge build emits the three
expected placeholder warnings. The audit rejects proof-source holes and collects
transitive axioms for every imported public declaration in both project namespaces.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The GitHub workflow calls Palomar's pinned full mechanical preflight, including
Comparator and the independent kernel checks. A local build and axiom audit alone
are not a claim that Palomar's full pipeline passed. The workflow's report is the
authoritative mechanical-preflight result at its exact source commit.

Palomar registration records a checked formalization; it is not expert peer review
or certification of novelty. Final registration follows the submission review.
