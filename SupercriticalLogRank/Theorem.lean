module

public import SupercriticalLogRank.Assembly
public import SupercriticalLogRank.FiberBound
public import SupercriticalLogRank.RankTransfer
public import SupercriticalLogRank.ScoreLimit

@[expose] public section

/-! The supercritical log-rank law in the balanced exponential market. -/

namespace SupercriticalLogRank

open Filter Set
open scoped Topology

/-- The logarithmic rank limit holds whenever the nonnegative costs have a logarithmic
scale limit below one. The lower supercritical assumption is unnecessary. -/
theorem logRankLaw (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hScale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ)) atTop (𝓝 ρ)) :
    ∀ t ∈ Ioo ρ 1, Tendsto
      (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  apply tendsto_conditionalRankProbability_of_score_limits ε hε hρ
    (fun _ ht ↦ tendsto_conditionedMarket_firmScore ε ρ hε hρ hScale ht)
    (fun _ ht ↦ tendsto_conditionedMarket_workerScore ε ρ hε hρ hScale ht)
  intro hX hY
  exact tendsto_conditioned_rankRatio_deviation ε hε hX hY

/-- The exact supercritical log-rank statement in Formal Conjectures issue #7827. -/
theorem supercriticalLogRankLaw (ε : ℕ → ℝ) (ρ : ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (_hSupercritical : Tendsto (fun k : ℕ ↦
      let n := k + 2
      (n : ℝ) * ε n / Real.log n) atTop atTop)
    (hScale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ)) atTop (𝓝 ρ)) :
    ∀ t ∈ Ioo ρ 1, Tendsto
      (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
      atTop (𝓝 ((t - ρ) / (1 - ρ))) :=
  logRankLaw ε ρ hε hρ hScale

end SupercriticalLogRank
