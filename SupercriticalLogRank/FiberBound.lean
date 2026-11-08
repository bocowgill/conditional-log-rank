module

public import SupercriticalLogRank.MarketBasics
public import SupercriticalLogRank.RankTransfer

@[expose] public section

/-! A fiberwise probability bound transfers to the conditioned market. -/

namespace SupercriticalLogRank

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Outside a set of diagonal scores of small conditional probability, a
uniform bound on the conditional fiber probabilities bounds the market event. -/
theorem conditionedMarket_preimage_le_of_fiber {n : ℕ} {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    {A : Set (ScoreSpace n)} (hA : MeasurableSet A) {B : Set (Vec n × Vec n)}
    (hB : MeasurableSet B)
    (hPoint : ∀ᵐ xy ∂diagonalScoreMeasure n, xy ∉ B →
      offRestrictedScoreMeasure (Real.exp (-ε)) xy (Prod.mk xy ⁻¹' A) ≤
        ENNReal.ofReal c * offRestrictedScoreMeasure (Real.exp (-ε)) xy univ) :
    (conditionedMarket n ε).real (splitScores n ⁻¹' A) ≤
      (conditionedMarket n ε).real
        ((fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' B) + c := by
  let μ := conditionedMarket n ε
  let : IsProbabilityMeasure μ := conditionedMarket_isProbability n hε
  let bad : Set (ScoreSpace n) := B ×ˢ univ
  let goodEvent := A ∩ badᶜ
  let a := Real.exp (-ε)
  have ha : a ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hgood : MeasurableSet goodEvent := hA.inter (hB.prod MeasurableSet.univ).compl
  have htotalMeas : AEMeasurable
      (fun xy ↦ offRestrictedScoreMeasure a xy univ) (diagonalScoreMeasure n) := by
    have hm : Measurable (fun xy : Vec n × Vec n ↦
        ENNReal.ofReal (stabilityKernel (a ^ 2) xy.1 xy.2)) :=
      (continuous_stabilityKernel n _).measurable.ennreal_ofReal
    refine hm.aemeasurable.congr ?_
    filter_upwards [ae_diagonalScoreMeasure_mem n] with xy hxy
    exact (offRestrictedScoreMeasure_univ ha hxy).symm
  have htotal :
      (∫⁻ xy, offRestrictedScoreMeasure a xy univ ∂diagonalScoreMeasure n) =
        marketMeasure n (stableEvent n ε) := by
    simpa [a] using
      (marketMeasure_stable_splitScores ε (MeasurableSet.univ : MeasurableSet (univ : Set (ScoreSpace n)))).symm
  have hraw :
      marketMeasure n (stableEvent n ε ∩ splitScores n ⁻¹' goodEvent) ≤
        ENNReal.ofReal c * marketMeasure n (stableEvent n ε) := by
    rw [marketMeasure_stable_splitScores ε hgood, ← htotal,
      ← lintegral_const_mul'' _ htotalMeas]
    apply lintegral_mono_ae
    filter_upwards [hPoint] with xy hxy
    by_cases hmem : xy ∈ B
    · have hfiber : Prod.mk xy ⁻¹' goodEvent = ∅ := by
        ext w
        simp [goodEvent, bad, hmem]
      rw [hfiber, measure_empty]
      exact zero_le
    · refine (measure_mono ?_).trans (hxy hmem)
      exact preimage_mono inter_subset_left
  have hreal : μ.real (splitScores n ⁻¹' goodEvent) ≤ c := by
    change (conditionedMarket n ε).real (splitScores n ⁻¹' goodEvent) ≤ c
    rw [conditionedMarket_real]
    refine (div_le_iff₀ (marketMeasure_real_stable_pos n hε)).2 ?_
    have hfinite : ENNReal.ofReal c * marketMeasure n (stableEvent n ε) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have hh := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfinite).2 hraw
    simpa only [measureReal_def, ENNReal.toReal_ofReal_mul c _ hc] using hh
  have hbad : splitScores n ⁻¹' bad =
      (fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' B := by
    ext p
    simp [splitScores, bad]
  have hsub : splitScores n ⁻¹' A ⊆
      splitScores n ⁻¹' bad ∪ splitScores n ⁻¹' goodEvent := by
    intro p hp
    by_cases hb : splitScores n p ∈ bad
    · exact Or.inl hb
    · exact Or.inr ⟨hp, hb⟩
  calc
    μ.real (splitScores n ⁻¹' A) ≤
        μ.real (splitScores n ⁻¹' bad ∪ splitScores n ⁻¹' goodEvent) := measureReal_mono hsub
    _ ≤ μ.real (splitScores n ⁻¹' bad) + μ.real (splitScores n ⁻¹' goodEvent) :=
      measureReal_union_le _ _
    _ ≤ _ := by rw [hbad]; linarith [hreal]

/-- Diagonal uniform scores are strictly between zero and one almost everywhere. -/
theorem ae_diagonalScoreMeasure_mem_interior (n : ℕ) :
    ∀ᵐ xy ∂diagonalScoreMeasure n,
      (∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1) := by
  let C : Set (Vec n) := univ.pi (fun _ ↦ Ioo (0 : ℝ) 1)
  have hC : MeasurableSet C :=
    MeasurableSet.pi countable_univ (fun _ _ ↦ measurableSet_Ioo)
  have heq : vectorScoreMeasure n = volume.restrict C := by
    unfold C vectorScoreMeasure
    rw [volume_pi, Measure.restrict_pi_pi]
    congr 1
    funext i
    exact restrict_Ioo_eq_restrict_Icc.symm
  rw [diagonalScoreMeasure, heq, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hC.prod hC)] with xy hxy
  exact ⟨fun i ↦ hxy.1 i (mem_univ i), fun i ↦ hxy.2 i (mem_univ i)⟩

/-- The rank-to-score ratio concentrates in the conditioned market once the
two diagonal score tails vanish and the fiberwise deviation bound holds. -/
theorem tendsto_conditioned_rankRatio_deviation (ε : ℕ → ℝ)
    (hε : ∀ n ≥ 2, 0 ≤ ε n)
    (hX : ∀ C > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
      {p | scoreSum (diagonalFirmScores p) ≤ C}) atTop (𝓝 0))
    (hY : ∀ c > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
      {p | c < scoreSum (diagonalWorkerScores p) / ((k + 2 : ℕ) : ℝ)}) atTop (𝓝 0)) :
    ∀ η > 0, Tendsto (fun k : ℕ ↦ (conditionedMarket (k + 2) (ε (k + 2))).real
      {p | η < |(firmRankSum p : ℝ) / (((k + 2 : ℕ) : ℝ) *
        scoreSum (diagonalFirmScores p)) - 1|}) atTop (𝓝 0) := by
  intro η hη
  let C : ℝ := max 1 (6 / η)
  let c : ℝ := η / 6
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hc : 0 < c := by dsimp [c]; positivity
  have hErr : Tendsto (fun k : ℕ ↦ 4 / (η ^ 2 * ((k + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    exact ((tendsto_const_div_atTop_nhds_zero_nat (4 / η ^ 2)).comp
      (tendsto_add_atTop_nat 2)).congr (fun k ↦ div_div _ _ ((k + 2 : ℕ) : ℝ))
  have hOne : Tendsto (fun k : ℕ ↦ 1 / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)
  have hlim := ((hX C hC).add (hY c hc)).add hErr
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [(tendsto_order.1 hOne).2 c hc] with k hOnek
  let n := k + 2
  let a := Real.exp (-(ε n))
  let μ := conditionedMarket n (ε n)
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hεn : 0 ≤ ε n := hε n (by dsimp [n]; omega)
  let : IsProbabilityMeasure μ := conditionedMarket_isProbability n hεn
  have ha : a ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  let D : Profile n → Vec n × Vec n := fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)
  let A : Set (ScoreSpace n) :=
    {w | η < |splitFirmRank w / ((n : ℝ) * scoreSum w.1.1) - 1|}
  let B₁ : Set (Vec n × Vec n) := {xy | scoreSum xy.1 ≤ C}
  let B₂ : Set (Vec n × Vec n) := {xy | c < scoreSum xy.2 / (n : ℝ)}
  let B := B₁ ∪ B₂
  have hA : MeasurableSet A := by
    have hscore : Measurable (fun w : ScoreSpace n ↦ scoreSum w.1.1) :=
      (measurable_scoreSum n).comp measurable_fst.fst
    exact measurableSet_lt measurable_const (((measurable_splitFirmRank n).div
      (measurable_const.mul hscore)).sub measurable_const).abs
  have hB₁ : MeasurableSet B₁ :=
    measurableSet_le ((measurable_scoreSum n).comp measurable_fst) measurable_const
  have hB₂ : MeasurableSet B₂ :=
    measurableSet_lt measurable_const (((measurable_scoreSum n).comp measurable_snd).div_const _)
  have hPoint : ∀ᵐ xy ∂diagonalScoreMeasure n, xy ∉ B →
      offRestrictedScoreMeasure a xy (Prod.mk xy ⁻¹' A) ≤
        ENNReal.ofReal (4 / (η ^ 2 * (n : ℝ))) * offRestrictedScoreMeasure a xy univ := by
    filter_upwards [ae_diagonalScoreMeasure_mem_interior n] with xy hxy
    intro hout
    have hx : C < scoreSum xy.1 := lt_of_not_ge (fun hh ↦ hout (Or.inl hh))
    have hy : scoreSum xy.2 / (n : ℝ) ≤ c := le_of_not_gt (fun hh ↦ hout (Or.inr hh))
    have hx1 : 1 ≤ scoreSum xy.1 := (le_max_left _ _).trans hx.le
    have hx6 : 6 / η ≤ scoreSum xy.1 := (le_max_right _ _).trans hx.le
    have hxi : 1 / scoreSum xy.1 ≤ c := by
      apply (div_le_iff₀ (zero_lt_one.trans_le hx1)).2
      have hh := (div_le_iff₀ hη).1 hx6
      dsimp [c]
      nlinarith
    have ha2 : a ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
    have hys : 0 ≤ scoreSum xy.2 := Finset.sum_nonneg fun i _ ↦ (hxy.2 i).1.le
    have hy' : a ^ 2 * scoreSum xy.2 / (n : ℝ) ≤ c :=
      (div_le_div_of_nonneg_right (mul_le_of_le_one_left hys ha2) hn0.le).trans hy
    have hbias :
        1 / scoreSum xy.1 + 1 / (n : ℝ) + a ^ 2 * scoreSum xy.2 / (n : ℝ) ≤ η / 2 := by
      change 1 / (n : ℝ) < c at hOnek
      dsimp [c] at hxi hy' hOnek
      linarith
    exact offRestricted_scoreRank_deviation_le hn ha hη hxy.1 hxy.2 hx1 hbias
  have hbound := conditionedMarket_preimage_le_of_fiber hεn
    (show 0 ≤ 4 / (η ^ 2 * (n : ℝ)) by positivity) hA (hB₁.union hB₂) hPoint
  have hpreA : splitScores n ⁻¹' A =
      {p | η < |(firmRankSum p : ℝ) / ((n : ℝ) * scoreSum (diagonalFirmScores p)) - 1|} := by
    ext p
    change (η < |splitFirmRank (splitScores n p) /
      ((n : ℝ) * scoreSum (diagonalFirmScores p)) - 1|) ↔ _
    rw [splitFirmRank_splitScores]
    rfl
  have hbad : μ.real (D ⁻¹' B) ≤
      μ.real {p | scoreSum (diagonalFirmScores p) ≤ C} +
      μ.real {p | c < scoreSum (diagonalWorkerScores p) / (n : ℝ)} := by
    rw [show B = B₁ ∪ B₂ from rfl, preimage_union]
    exact measureReal_union_le (D ⁻¹' B₁) (D ⁻¹' B₂)
  rw [← hpreA]
  exact hbound.trans (by
    change μ.real (D ⁻¹' B) + _ ≤ _
    linarith [hbad])

end SupercriticalLogRank
