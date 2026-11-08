module

public import SupercriticalLogRank

/-!
# Conditional logarithmic partner ranks in exponential matching markets

The market has `n` firms and `n` workers. All `2 * n^2` directed utilities are
independent rate-one exponentials. The fixed diagonal matching is stable at cost
`ε` if no unmatched pair would both gain strictly more than `ε` by switching.

The rank of an assigned partner is one-based, with higher utility ranked better.
We condition the entire random market on stability of this fixed matching.
This is not a lottery drawn from the stable matchings of an ordinary random market.

Pittel and Rudov ask about partner ranks under relaxed stability. Their work
motivates the model, rather than states the precise limit proved here. See
<https://doi.org/10.1007/s00182-026-01016-x> and Appendix C of
<https://krudov.com/papers/JMP_Kirill_Rudov.pdf>.
-/

@[expose] public section

namespace ConditionalLogRank

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- Two directed utility arrays, indexed by side, firm, and worker. -/
abbrev Profile (n : ℕ) := (Bool × Fin n × Fin n) → ℝ

/-- The ordinary product law of independent rate-one exponential utilities. -/
noncomputable def marketMeasure (n : ℕ) : Measure (Profile n) :=
  Measure.pi fun _ ↦ expMeasure 1

/-- Stability of the diagonal matching: both gains must strictly exceed the cost. -/
def stableEvent (n : ℕ) (ε : ℝ) : Set (Profile n) :=
  {p | ∀ i j : Fin n, i ≠ j →
    ¬ (p (false, i, i) + ε < p (false, i, j) ∧
      p (true, j, j) + ε < p (true, i, j))}

open scoped Classical in
/-- The sum of firms' one-based assigned-partner ranks; ties have probability zero. -/
noncomputable def firmRankSum {n : ℕ} (p : Profile n) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, if p (false, i, i) ≤ p (false, i, j) then 1 else 0

/-- Average firm rank at most `n ^ t`, equivalently total rank at most `n ^ (1 + t)`. -/
def rankCutoffEvent (n : ℕ) (t : ℝ) : Set (Profile n) :=
  {p | (firmRankSum p : ℝ) ≤ (n : ℝ) ^ (1 + t)}

/-- The rank-cutoff probability conditional on stability of the fixed diagonal matching. -/
noncomputable def conditionalRankProbability (n : ℕ) (ε t : ℝ) : ℝ :=
  let μ := marketMeasure n
  μ.real (stableEvent n ε ∩ rankCutoffEvent n t) / μ.real (stableEvent n ε)

/-- The conditioning event has positive probability at every nonnegative cost. -/
theorem stability_probability_pos (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < (marketMeasure n).real (stableEvent n ε) := by
  exact SupercriticalLogRank.marketMeasure_real_stable_pos n hε

/-- If `2 * ε n / log n → ρ ∈ [0, 1)`, the conditional rank CDF at every
`ρ < t < 1` tends to `(t - ρ) / (1 - ρ)`. Sizes run through `k + 2`. -/
theorem logRankLaw (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hScale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ)) atTop (𝓝 ρ)) :
    ∀ t ∈ Ioo ρ 1, Tendsto
      (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  exact SupercriticalLogRank.logRankLaw ε ρ hε hρ hScale

/-- The same conditional law with the additional supercritical hypothesis
`n * ε n / log n → ∞`. This is a corollary of `logRankLaw`. -/
theorem supercriticalLogRankLaw (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hSupercritical : Tendsto (fun k : ℕ ↦
      let n := k + 2
      (n : ℝ) * ε n / Real.log n) atTop atTop)
    (hScale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ)) atTop (𝓝 ρ)) :
    ∀ t ∈ Ioo ρ 1, Tendsto
      (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  exact SupercriticalLogRank.supercriticalLogRankLaw ε ρ hε hρ hSupercritical hScale

end ConditionalLogRank
