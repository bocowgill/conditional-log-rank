module

public import SupercriticalLogRank.MarketBasics
public import SupercriticalLogRank.ConditionalIntegral
public import SupercriticalLogRank.SimplexConcentration
public import SupercriticalLogRank.ExactRadial
public import SupercriticalLogRank.InteriorLimit
public import SupercriticalLogRank.RadialLimit

@[expose] public section

/-! The conditional diagonal score limits from the radial integral. -/

namespace SupercriticalLogRank

open Filter MeasureTheory Set
open scoped Topology
open ProbabilityTheory (expMeasure isProbabilityMeasure_expMeasure)

private theorem marketMeasure_ae_coordinate_nonneg (n : ℕ) :
    ∀ᵐ p ∂marketMeasure n, ∀ i, 0 ≤ p i := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  rw [ae_all_iff]
  intro i
  have h := measurePreserving_eval (μ := fun _ : Bool × Fin n × Fin n ↦ expMeasure 1) i
  exact h.quasiMeasurePreserving.ae (ae_pos_expMeasure_one.mono fun _ h ↦ h.le)

private theorem marketMeasure_ae_firmScore_le (n : ℕ) :
    ∀ᵐ p ∂marketMeasure n, scoreSum (diagonalFirmScores p) ≤ (n : ℝ) := by
  filter_upwards [marketMeasure_ae_coordinate_nonneg n] with p hp
  unfold scoreSum
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hp (false, i, i)))
    _ = (n : ℝ) := by simp

/-- A cutoff at the size of the market includes all firm diagonal scores. -/
theorem marketMeasure_real_stable_firmScore_total (n : ℕ) (ε : ℝ) :
    (marketMeasure n).real (stableEvent n ε ∩
      {p | scoreSum (diagonalFirmScores p) ≤ (n : ℝ)}) =
    (marketMeasure n).real (stableEvent n ε) := by
  apply measureReal_congr
  filter_upwards [marketMeasure_ae_firmScore_le n] with p hp
  exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hp⟩⟩

/-- The shared prefactor in the numerator and denominator cancels in the score CDF. -/
theorem conditionedMarket_real_firmScoreCutoff_of_radial (n : ℕ) (ε c D : ℝ)
    (hD : D ≠ 0)
    (hcut : ∀ b : ℝ, 0 ≤ b →
      (marketMeasure n).real (stableEvent n ε ∩
        {p | scoreSum (diagonalFirmScores p) ≤ b}) =
      D * ∫ s in Icc 0 b, radialDensity n (Real.exp (-2 * ε)) s / s)
    (hc : 0 ≤ c) :
    (conditionedMarket n ε).real {p | scoreSum (diagonalFirmScores p) ≤ c} =
      (∫ s in Icc 0 c, radialDensity n (Real.exp (-2 * ε)) s / s) /
        ∫ s in Icc 0 (n : ℝ), radialDensity n (Real.exp (-2 * ε)) s / s := by
  rw [conditionedMarket_real, hcut c hc, ← marketMeasure_real_stable_firmScore_total,
    hcut (n : ℝ) (by positivity)]
  exact mul_div_mul_left _ _ hD

/-- Given the exact radial cutoff identity and the interior estimates, the market score CDF
converges to the interior CDF of the uniform law on `[ρ, 1]`. -/
theorem tendsto_conditionedMarket_firmScore_of_radial
    (ε : ℕ → ℝ) (ρ : ℝ) (hε : ∀ n ≥ 2, 0 ≤ ε n)
    (hρ : ρ ∈ Ico 0 1)
    (hscale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ))
      atTop (𝓝 ρ))
    (hcut : ∀ k : ℕ, ∃ D : ℝ, D ≠ 0 ∧ ∀ b : ℝ, 0 ≤ b →
      (marketMeasure (k + 2)).real (stableEvent (k + 2) (ε (k + 2)) ∩
        {p | scoreSum (diagonalFirmScores p) ≤ b}) =
      D * ∫ s in Icc 0 b, radialDensity (k + 2) (Real.exp (-2 * ε (k + 2))) s / s)
    (hwindow : ∀ (δ : ℝ), 0 < δ → ∀ (η : ℝ), 0 < η → ∀ᶠ n in atTop, ∀ s : ℝ,
      ((n + 2 : ℕ) : ℝ) ^ δ / Real.exp (-2 * ε (n + 2)) ≤ s →
      s ≤ ((n + 2 : ℕ) : ℝ) ^ (1 - δ) →
      |radialDensity (n + 2) (Real.exp (-2 * ε (n + 2))) s - Real.exp (-1)| < η)
    {t : ℝ} (ht : t ∈ Ioo ρ 1) :
    Tendsto (fun n : ℕ ↦ (conditionedMarket (n + 2) (ε (n + 2))).real
      {p | scoreSum (diagonalFirmScores p) ≤ ((n + 2 : ℕ) : ℝ) ^ t})
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  let q : ℕ → ℝ := fun n ↦ Real.exp (-2 * ε (n + 2))
  let H : ℕ → ℝ → ℝ := fun n ↦ radialDensity (n + 2) (q n)
  have hq (n : ℕ) : q n ∈ Ioc 0 1 := by
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
    linarith [hε (n + 2) (by omega)]
  have hqscale :
      Tendsto (fun n ↦ -Real.log (q n) / logMarketSize n) atTop (𝓝 ρ) := by
    simpa only [q, logMarketSize, Real.log_exp, neg_mul, neg_neg] using hscale
  have hb (n : ℕ) (s : ℝ) (hs : 0 < s) :
      H n s ∈ Icc 0 (min (Real.exp 2) ((q n * s) ^ (n + 2))) := by
    apply radialDensity_bounds (hq n) hs
    filter_upwards [ae_simplexLaw (n + 2) (by omega)] with u hu
    exact ⟨fun i ↦ (hu.1 i).le, hu.2⟩
  have hlim := radialMass_ratio_tendsto H q ρ t ht.1.le ht.2.le hρ.2 hq hqscale
    (fun n ↦ measurable_radialDensity _ _)
    (fun n s hs ↦ (hb n s hs).1)
    (fun n s hs ↦ (hb n s hs).2.trans (min_le_left _ _))
    (fun n s hs ↦ (hb n s hs).2.trans (min_le_right _ _))
    hwindow
  refine hlim.congr' (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨D, hD, hDcut⟩ := hcut n
  exact (conditionedMarket_real_firmScoreCutoff_of_radial (n + 2) _ _ D hD hDcut
    (Real.rpow_nonneg (by positivity) _)).symm

/-- The worker score limit follows from equality of the two score CDFs. -/
theorem tendsto_conditionedMarket_workerScore_of_firm (ε : ℕ → ℝ) (ρ t : ℝ)
    (hfirm : Tendsto (fun n : ℕ ↦ (conditionedMarket (n + 2) (ε (n + 2))).real
      {p | scoreSum (diagonalFirmScores p) ≤ ((n + 2 : ℕ) : ℝ) ^ t})
      atTop (𝓝 ((t - ρ) / (1 - ρ)))) :
    Tendsto (fun n : ℕ ↦ (conditionedMarket (n + 2) (ε (n + 2))).real
      {p | scoreSum (diagonalWorkerScores p) ≤ ((n + 2 : ℕ) : ℝ) ^ t})
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  refine hfirm.congr fun n ↦ ?_
  exact (conditionedMarket_real_workerScoreCutoff_eq_firm _ _ _).symm

/-- The limiting CDF of the firm diagonal score, conditional on stability. -/
theorem tendsto_conditionedMarket_firmScore
    (ε : ℕ → ℝ) (ρ : ℝ) (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hscale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ))
      atTop (𝓝 ρ)) {t : ℝ} (ht : t ∈ Ioo ρ 1) :
    Tendsto (fun n : ℕ ↦ (conditionedMarket (n + 2) (ε (n + 2))).real
      {p | scoreSum (diagonalFirmScores p) ≤ ((n + 2 : ℕ) : ℝ) ^ t})
      atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  let q : ℕ → ℝ := fun n ↦ Real.exp (-2 * ε (n + 2))
  have hq (n : ℕ) : q n ∈ Ioc 0 1 := by
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
    linarith [hε (n + 2) (by omega)]
  refine tendsto_conditionedMarket_firmScore_of_radial ε ρ hε hρ hscale
    (fun k ↦ ?_) (fun δ hδ η hη ↦ eventually_radialDensity_interior q δ hδ hq η hη) ht
  refine ⟨(q k)⁻¹ ^ (k + 2) / ((k + 1).factorial : ℝ), ?_, ?_⟩
  · exact div_ne_zero (pow_ne_zero _ (inv_ne_zero (hq k).1.ne'))
      (by exact_mod_cast Nat.factorial_ne_zero (k + 1))
  · intro b _
    rw [marketMeasure_real_stable_firmScoreCutoff _ _ _ (hε _ (by omega))]
    exact integral_scoreKernel_eq_radial (k + 1) (hq k)

/-- The worker side has the same conditional score limit. -/
theorem tendsto_conditionedMarket_workerScore
    (ε : ℕ → ℝ) (ρ : ℝ) (hε : ∀ n ≥ 2, 0 ≤ ε n) (hρ : ρ ∈ Ico 0 1)
    (hscale : Tendsto (fun k : ℕ ↦ 2 * ε (k + 2) / Real.log (k + 2 : ℕ))
      atTop (𝓝 ρ)) {t : ℝ} (ht : t ∈ Ioo ρ 1) :
    Tendsto (fun n : ℕ ↦ (conditionedMarket (n + 2) (ε (n + 2))).real
      {p | scoreSum (diagonalWorkerScores p) ≤ ((n + 2 : ℕ) : ℝ) ^ t})
      atTop (𝓝 ((t - ρ) / (1 - ρ))) :=
  tendsto_conditionedMarket_workerScore_of_firm ε ρ t
    (tendsto_conditionedMarket_firmScore ε ρ hε hρ hscale ht)

end SupercriticalLogRank
