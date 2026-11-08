module

public import SupercriticalLogRank.LogVariables
public import SupercriticalLogRank.ScoreConsequences
public import SupercriticalLogRank.RankTransfer
public import SupercriticalLogRank.ScoreLimit
public import SupercriticalLogRank.InteriorLimit

@[expose] public section

/-!
# From the score limit to the rank law

The power cutoff for ranks is the CDF cutoff for the logarithmic rank.
The score CDF and concentration of the rank-to-score ratio imply the
conditional rank limit.
-/

namespace SupercriticalLogRank

open Filter MeasureTheory Set
open scoped Topology

/-- The interior CDF for the firm score and relative rank concentration
imply the rank cutoff limit in the original market. -/
theorem tendsto_conditionalRankProbability_of_score_and_ratio (ε : ℕ → ℝ) {ρ : ℝ}
    (hε : ∀ n ≥ 2, 0 ≤ ε n)
    (hScore : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | scoreSum (diagonalFirmScores p) ≤ ((k + 2 : ℕ) : ℝ) ^ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ))))
    (hRatio : Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | 1 / 2 < |((firmRankSum p : ℝ) / ((k + 2 : ℕ) : ℝ)) /
          scoreSum (diagonalFirmScores p) - 1|}) atTop (𝓝 0)) :
    ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
        atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  let μ (k : ℕ) := conditionedMarket (k + 2) (ε (k + 2))
  let (k : ℕ) : IsProbabilityMeasure (μ k) :=
    conditionedMarket_isProbability _ (hε _ (by omega))
  let X (k : ℕ) (p : Profile (k + 2)) := scoreSum (diagonalFirmScores p)
  let Y (k : ℕ) (p : Profile (k + 2)) := (firmRankSum p : ℝ) / ((k + 2 : ℕ) : ℝ)
  let s (k : ℕ) := Real.log ((k + 2 : ℕ) : ℝ)
  have hn₁ (k : ℕ) : 1 < ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < k + 2 by omega)
  have hXpos (k : ℕ) (p : Profile (k + 2)) : 0 < X k p :=
    diagonalFirmScoreSum_pos (by omega) p
  have hYpos (k : ℕ) (p : Profile (k + 2)) : 0 < Y k p := by
    have hr : ((k + 2 : ℕ) : ℝ) ≤ (firmRankSum p : ℝ) := by
      exact_mod_cast card_le_firmRankSum p
    exact div_pos (lt_of_lt_of_le (zero_lt_one.trans (hn₁ k)) hr) (by positivity)
  have hs (k : ℕ) : 0 < s k := Real.log_pos (hn₁ k)
  have hsLim : Tendsto s atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hLogX : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k ↦ (μ k).real {p | Real.log (X k p) / s k ≤ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
    intro t ht
    apply (hScore t ht).congr
    intro k
    exact (measureReal_logScore_eq_power (μ k)
      (Eventually.of_forall (hXpos k)) (hn₁ k)).symm
  have hperturb := tendsto_logDeviation_of_ratioDeviation μ X Y s hXpos hYpos hs hsLim hRatio
  intro t ht
  apply (tendsto_uniformCDF_of_perturbation μ
    (fun k p ↦ Real.log (X k p) / s k) (fun k p ↦ Real.log (Y k p) / s k)
    hLogX hperturb t ht).congr
  intro k
  change (μ k).real {p | Real.log (Y k p) / s k ≤ t} =
    conditionalRankProbability (k + 2) (ε (k + 2)) t
  have hset : {p | Real.log (Y k p) / s k ≤ t} = rankCutoffEvent (k + 2) t :=
    Set.ext fun p ↦ logRank_le_iff_mem_rankCutoffEvent (by omega) p t
  rw [hset, conditionedMarket_real_rankCutoff]

/-- The logarithmic rank limit follows from the two score CDFs once the
conditional rank concentration estimate has been verified. -/
theorem tendsto_conditionalRankProbability_of_score_limits (ε : ℕ → ℝ) {ρ : ℝ}
    (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hFirm : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | scoreSum (diagonalFirmScores p) ≤ ((k + 2 : ℕ) : ℝ) ^ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ))))
    (hWorker : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | scoreSum (diagonalWorkerScores p) ≤ ((k + 2 : ℕ) : ℝ) ^ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ))))
    (hConcentration :
      (∀ C > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | scoreSum (diagonalFirmScores p) ≤ C}) atTop (𝓝 0)) →
      (∀ c > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | c < scoreSum (diagonalWorkerScores p) / ((k + 2 : ℕ) : ℝ)}) atTop (𝓝 0)) →
      ∀ δ > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | δ < |(firmRankSum p : ℝ) /
          (((k + 2 : ℕ) : ℝ) * scoreSum (diagonalFirmScores p)) - 1|}) atTop (𝓝 0)) :
    ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
        atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  let μ (k : ℕ) := conditionedMarket (k + 2) (ε (k + 2))
  let (k : ℕ) : IsProbabilityMeasure (μ k) :=
    conditionedMarket_isProbability _ (hε _ (by omega))
  have hX (C : ℝ) (_ : 0 < C) :=
    tendsto_measureReal_score_le_const μ (fun _ p ↦ scoreSum (diagonalFirmScores p)) hρ hFirm C
  have hY (c : ℝ) (hc : 0 < c) :=
    tendsto_measureReal_score_over_size_tail μ (fun _ p ↦ scoreSum (diagonalWorkerScores p))
      (fun k ↦ (measurable_scoreSum (k + 2)).comp (by
        unfold diagonalWorkerScores
        fun_prop (disch := exact measurable_pi_apply _))) hρ hWorker hc
  apply tendsto_conditionalRankProbability_of_score_and_ratio ε hε hFirm
  simpa only [div_div] using hConcentration hX hY (1 / 2) (by norm_num)

/-- The exact radial cutoff formula and conditional rank concentration close
the score and rank limits under the stated logarithmic cost window. -/
theorem tendsto_conditionalRankProbability_of_radial_and_concentration
    (ε : ℕ → ℝ) (ρ : ℝ) (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hscale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ))
      atTop (𝓝 ρ))
    (hcut : ∀ k : ℕ, ∃ D : ℝ, D ≠ 0 ∧ ∀ b : ℝ, 0 ≤ b →
      (marketMeasure (k + 2)).real (stableEvent (k + 2) (ε (k + 2)) ∩
        {p | scoreSum (diagonalFirmScores p) ≤ b}) =
      D * ∫ s in Icc 0 b, radialDensity (k + 2) (Real.exp (-2 * ε (k + 2))) s / s)
    (hConcentration :
      (∀ C > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | scoreSum (diagonalFirmScores p) ≤ C}) atTop (𝓝 0)) →
      (∀ c > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | c < scoreSum (diagonalWorkerScores p) / ((k + 2 : ℕ) : ℝ)}) atTop (𝓝 0)) →
      ∀ δ > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
        {p | δ < |(firmRankSum p : ℝ) /
          (((k + 2 : ℕ) : ℝ) * scoreSum (diagonalFirmScores p)) - 1|}) atTop (𝓝 0)) :
    ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ conditionalRankProbability (k + 2) (ε (k + 2)) t)
        atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  let q (k : ℕ) := Real.exp (-2 * ε (k + 2))
  have hq (k : ℕ) : q k ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
    linarith [hε (k + 2) (by omega)]
  have hFirm t ht := tendsto_conditionedMarket_firmScore_of_radial ε ρ hε hρ hscale hcut
    (fun δ hδ η hη ↦ eventually_radialDensity_interior q δ hδ hq η hη) (t := t) ht
  exact tendsto_conditionalRankProbability_of_score_limits ε hε hρ hFirm
    (fun t ht ↦ tendsto_conditionedMarket_workerScore_of_firm ε ρ t (hFirm t ht))
    hConcentration

end SupercriticalLogRank
