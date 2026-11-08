module

public import SupercriticalLogRank.ConditionalIntegral

@[expose] public section

/-!
# Transfer from scores to ranks

The conditional rank calculation separates into the probability of a rank indicator,
the variance bound for a sum of independent indicators, and the limiting CDF comparison.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators

namespace SupercriticalLogRank

/-- Bounds for the rank indicator probability obtained by removing the blocking rectangle. -/
theorem rankIndicatorProbability_bounds {x y q : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hden : 0 < 1 - q * x * y) :
    x * (1 - q * y) ≤ (x - q * x * y) / (1 - q * x * y) ∧
      (x - q * x * y) / (1 - q * x * y) ≤ x := by
  have hxy : 0 ≤ q * x * y := mul_nonneg (mul_nonneg hq.1 hx.1) hy.1
  have hqy : q * y ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq.2) hy.1, hy.2]
  have hnum : 0 ≤ x * (1 - q * y) := mul_nonneg hx.1 (sub_nonneg.mpr hqy)
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      x * (1 - q * y) * (1 - q * x * y) ≤ x * (1 - q * y) * 1 :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hxy) hnum
      _ = x - q * x * y := by ring
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hxy (sub_nonneg.mpr hx.2)]

section CDF

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]

private theorem scoreCDF_lower (X Y : ∀ n, Ω n → ℝ) (n : ℕ) (t δ : ℝ) :
    (μ n).real {ω | X n ω ≤ t - δ} - (μ n).real {ω | δ < |Y n ω - X n ω|}
      ≤ (μ n).real {ω | Y n ω ≤ t} := by
  have h : {ω | X n ω ≤ t - δ} ⊆ {ω | Y n ω ≤ t} ∪ {ω | δ < |Y n ω - X n ω|} := by
    intro ω hω
    rcases le_or_gt (Y n ω) t with h | h
    · exact Or.inl h
    · exact Or.inr ((show δ < Y n ω - X n ω by linarith [show X n ω ≤ t - δ from hω]).trans_le
        (le_abs_self _))
  exact sub_le_iff_le_add.2 ((measureReal_mono h).trans (measureReal_union_le _ _))

private theorem scoreCDF_upper (X Y : ∀ n, Ω n → ℝ) (n : ℕ) (t δ : ℝ) :
    (μ n).real {ω | Y n ω ≤ t} ≤
      (μ n).real {ω | X n ω ≤ t + δ} + (μ n).real {ω | δ < |Y n ω - X n ω|} := by
  have h : {ω | Y n ω ≤ t} ⊆ {ω | X n ω ≤ t + δ} ∪ {ω | δ < |Y n ω - X n ω|} := by
    intro ω hω
    rcases le_or_gt (X n ω) (t + δ) with h | h
    · exact Or.inl h
    · exact Or.inr ((show δ < -(Y n ω - X n ω) by linarith [show Y n ω ≤ t from hω]).trans_le
        (neg_le_abs _))
  exact (measureReal_mono h).trans (measureReal_union_le _ _)

/-- A vanishing perturbation in probability preserves the interior uniform CDF limit,
also when the probability space varies with the index. -/
theorem tendsto_uniformCDF_of_perturbation (X Y : ∀ n, Ω n → ℝ) {ρ : ℝ}
    (hX : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun n ↦ (μ n).real {ω | X n ω ≤ t}) atTop (𝓝 ((t - ρ) / (1 - ρ))))
    (hYX : ∀ δ > 0,
      Tendsto (fun n ↦ (μ n).real {ω | δ < |Y n ω - X n ω|}) atTop (𝓝 0)) :
    ∀ t ∈ Ioo ρ 1,
      Tendsto (fun n ↦ (μ n).real {ω | Y n ω ≤ t}) atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  intro t ht
  have hden : 0 < 1 - ρ := by linarith [ht.1, ht.2]
  let L := (t - ρ) / (1 - ρ)
  have hL : L * (1 - ρ) = t - ρ := div_mul_cancel₀ _ hden.ne'
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    let δ := min ((t - ρ) / 2) ((L - l) * (1 - ρ) / 2)
    have hδ : 0 < δ := lt_min (by linarith [ht.1]) (by
      have : 0 < L - l := sub_pos.mpr hl
      positivity)
    have hδ₁ : δ ≤ (t - ρ) / 2 := min_le_left _ _
    have hδ₂ : δ ≤ (L - l) * (1 - ρ) / 2 := min_le_right _ _
    have hgap : 0 < (L - l) * (1 - ρ) := mul_pos (sub_pos.mpr hl) hden
    have hl' : l < (t - δ - ρ) / (1 - ρ) := by
      apply (lt_div_iff₀ hden).2
      nlinarith only [hδ₂, hL, hgap]
    have hT := (hX (t - δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩).sub (hYX δ hδ)
    rw [sub_zero] at hT
    filter_upwards [(tendsto_order.1 hT).1 l hl'] with n hn
    exact hn.trans_le (scoreCDF_lower μ X Y n t δ)
  · intro u hu
    let δ := min ((1 - t) / 2) ((u - L) * (1 - ρ) / 2)
    have hδ : 0 < δ := lt_min (by linarith [ht.2]) (by
      have : 0 < u - L := sub_pos.mpr hu
      positivity)
    have hδ₁ : δ ≤ (1 - t) / 2 := min_le_left _ _
    have hδ₂ : δ ≤ (u - L) * (1 - ρ) / 2 := min_le_right _ _
    have hgap : 0 < (u - L) * (1 - ρ) := mul_pos (sub_pos.mpr hu) hden
    have hu' : (t + δ - ρ) / (1 - ρ) < u := by
      apply (div_lt_iff₀ hden).2
      nlinarith only [hδ₂, hL, hgap]
    have hT := (hX (t + δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩).add (hYX δ hδ)
    rw [add_zero] at hT
    filter_upwards [(tendsto_order.1 hT).2 u hu'] with n hn
    exact (scoreCDF_upper μ X Y n t δ).trans_lt hn

end CDF

section Bernoulli

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Conditioning a finite independent product on separate coordinate events preserves
the product structure and conditions each coordinate on its own event. -/
theorem cond_pi_box (B : ∀ i, Set (Ω i)) (hB : ∀ i, ν i (B i) ≠ 0) :
    cond (Measure.pi ν) (univ.pi B) = Measure.pi (fun i ↦ cond (ν i) (B i)) := by
  let (i : ι) : IsProbabilityMeasure (cond (ν i) (B i)) := cond_isProbabilityMeasure (hB i)
  symm
  refine Measure.pi_eq fun A hA ↦ ?_
  rw [cond_apply' (MeasurableSet.univ_pi hA), ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi]
  rw [ENNReal.prod_inv_distrib, ← Finset.prod_mul_distrib]
  · exact Finset.prod_congr rfl fun i _ ↦ (cond_apply' (hA i) (ν i)).symm
  · intro i _ j _ _
    exact Or.inl (hB i)

/-- The real-valued conditional mass is the usual ratio of real masses. -/
theorem cond_real_eq_div {α : Type*} [MeasurableSpace α] (m : Measure α) {B : Set α}
    (hB : MeasurableSet B) (A : Set α) :
    (cond m B).real A = m.real (B ∩ A) / m.real B := by
  rw [measureReal_def, cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  exact mul_comm _ _

noncomputable def countCoordinateEvents (A : ∀ i, Set (Ω i)) : (∀ i, Ω i) → ℝ :=
  ∑ i, fun ω ↦ (A i).indicator (fun _ ↦ (1 : ℝ)) (ω i)

private theorem memLp_indicator_one_real {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsFiniteMeasure m] {A : Set α} (hA : MeasurableSet A) :
    MemLp (A.indicator (fun _ ↦ (1 : ℝ))) 2 m :=
  (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet

/-- The count of coordinate events has a finite second moment. -/
theorem memLp_countCoordinateEvents (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (countCoordinateEvents A) 2 (Measure.pi ν) := by
  classical
  have h (i : ι) : MemLp (fun ω ↦ (A i).indicator (fun _ ↦ (1 : ℝ)) (ω i)) 2 (Measure.pi ν) :=
    (memLp_indicator_one_real (ν i) (hA i)).comp_measurePreserving (measurePreserving_eval _ i)
  exact memLp_finsetSum' Finset.univ (fun i _ ↦ h i)

/-- The mean of the count is the sum of the coordinate probabilities. -/
theorem integral_countCoordinateEvents (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) :
    ∫ ω, countCoordinateEvents A ω ∂Measure.pi ν = ∑ i, (ν i).real (A i) := by
  classical
  simp only [countCoordinateEvents, Finset.sum_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_comp_eval (memLp_indicator_one_real (ν i) (hA i)).aestronglyMeasurable]
    exact integral_indicator_one (hA i)
  · exact fun i _ ↦
      ((memLp_indicator_one_real (ν i) (hA i)).comp_measurePreserving
        (measurePreserving_eval _ i)).integrable one_le_two

/-- The variance of the count is at most the sum of the coordinate probabilities. -/
theorem variance_countCoordinateEvents_le (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) :
    variance (countCoordinateEvents A) (Measure.pi ν) ≤ ∑ i, (ν i).real (A i) := by
  classical
  unfold countCoordinateEvents
  rw [variance_sum_pi (fun i ↦ memLp_indicator_one_real (ν i) (hA i))]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  let ξ : Ω i → ℝ := (A i).indicator (fun _ ↦ 1)
  change variance ξ (ν i) ≤ _
  have hξ : ξ ^ 2 = ξ := by
    funext ω
    by_cases hω : ω ∈ A i <;> simp [ξ, hω]
  calc
    variance ξ (ν i) ≤ ∫ ω, (ξ ^ 2) ω ∂ν i :=
      variance_le_expectation_sq (memLp_indicator_one_real (ν i) (hA i)).aestronglyMeasurable
    _ = (ν i).real (A i) := by
      rw [hξ]
      exact integral_indicator_one (hA i)

/-- Chebyshev's inequality for a count of independent coordinate events. -/
theorem measureReal_countCoordinateEvents_deviation_le
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) {r : ℝ} (hr : 0 < r) :
    (Measure.pi ν).real {ω | r ≤ |countCoordinateEvents A ω - ∑ i, (ν i).real (A i)|}
      ≤ (∑ i, (ν i).real (A i)) / r ^ 2 := by
  classical
  rw [← integral_countCoordinateEvents ν A hA]
  have h := meas_ge_le_variance_div_sq (memLp_countCoordinateEvents ν A hA) hr
  have hvar := variance_countCoordinateEvents_le ν A hA
  have hnonneg := div_nonneg (variance_nonneg (countCoordinateEvents A) (Measure.pi ν)) (sq_nonneg r)
  calc
    _ ≤ variance (countCoordinateEvents A) (Measure.pi ν) / r ^ 2 := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ ≤ _ := by
      rw [integral_countCoordinateEvents ν A hA]
      exact div_le_div_of_nonneg_right hvar (sq_nonneg r)

end Bernoulli

section Pair

/-- If the forbidden event is contained in the event being counted, conditioning on
its complement subtracts the forbidden mass from both numerator and denominator. -/
theorem cond_compl_real_eq_div {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsProbabilityMeasure m] {A B : Set α} (hB : MeasurableSet B) (hBA : B ⊆ A) :
    (cond m Bᶜ).real A = (m.real A - m.real B) / (1 - m.real B) := by
  rw [cond_real_eq_div m hB.compl, inter_comm, ← sdiff_eq, measureReal_sdiff hBA hB,
    measureReal_compl hB, probReal_univ]

private theorem real_unitScoreMeasure_Iic {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    unitScoreMeasure.real (Iic z) = z := by
  have h : Iic z ∩ Icc (0 : ℝ) 1 = Icc 0 z := by
    ext a
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun ha ↦ ⟨ha.2.1, ha.1⟩, fun ha ↦ ⟨ha.2, ha.1, ha.2.trans hz.2⟩⟩
  rw [measureReal_def, unitScoreMeasure, Measure.restrict_apply measurableSet_Iic, h,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hz.1]

private theorem pair_uniform_blocking_mass {a x y : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    pairScoreMeasure.real (Iio (a * x) ×ˢ Iio (a * y)) = a ^ 2 * x * y := by
  have hax : a * x ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ha.1 hx.1, (mul_le_mul_of_nonneg_right ha.2 hx.1).trans (by simpa using hx.2)⟩
  have hay : a * y ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ha.1 hy.1, (mul_le_mul_of_nonneg_right ha.2 hy.1).trans (by simpa using hy.2)⟩
  rw [measureReal_def, pairScoreMeasure, Measure.prod_prod, ENNReal.toReal_mul,
    unitScoreMeasure_Iio hax.2, unitScoreMeasure_Iio hay.2, ENNReal.toReal_ofReal hax.1,
    ENNReal.toReal_ofReal hay.1]
  ring

/-- The exact conditional probability of a better or tied firm score in one off-diagonal
pair, given that the pair does not block. Both scores are independent uniforms before conditioning. -/
theorem pair_uniform_conditional_rank_mass {a x y : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (cond pairScoreMeasure (allowedScorePair a x y)).real (Iic x ×ˢ (univ : Set ℝ))
      = (x - a ^ 2 * x * y) / (1 - a ^ 2 * x * y) := by
  have hsub : Iio (a * x) ×ˢ Iio (a * y) ⊆ Iic x ×ˢ (univ : Set ℝ) :=
    Set.prod_mono (fun _ hz ↦ (mem_Iio.mp hz).le.trans (by
      simpa using mul_le_mul_of_nonneg_right ha.2 hx.1)) (subset_univ _)
  have hrank : pairScoreMeasure.real (Iic x ×ˢ (univ : Set ℝ)) = x := by
    simp [pairScoreMeasure, real_unitScoreMeasure_Iic hx]
  rw [allowedScorePair, cond_compl_real_eq_div _ (measurableSet_Iio.prod measurableSet_Iio) hsub, hrank,
    pair_uniform_blocking_mass ha hx hy]

end Pair

section Logarithms

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]

/-- If a ratio of positive variables is usually between one half and three halves, its
logarithm divided by any deterministic scale tending to infinity converges in probability to zero. -/
theorem tendsto_logDeviation_of_ratioDeviation (X Y : ∀ n, Ω n → ℝ) (s : ℕ → ℝ)
    (hX : ∀ n ω, 0 < X n ω) (hY : ∀ n ω, 0 < Y n ω)
    (hs : ∀ n, 0 < s n) (hsLim : Tendsto s atTop atTop)
    (hRatio : Tendsto (fun n ↦ (μ n).real {ω | 1 / 2 < |Y n ω / X n ω - 1|}) atTop (𝓝 0)) :
    ∀ δ > 0,
      Tendsto (fun n ↦ (μ n).real
        {ω | δ < |Real.log (Y n ω) / s n - Real.log (X n ω) / s n|}) atTop (𝓝 0) := by
  intro δ hδ
  have hScale : ∀ᶠ n in atTop, Real.log 2 / δ ≤ s n :=
    hsLim.eventually (eventually_ge_atTop _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRatio
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [hScale] with n hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hbad
  have hr : |Y n ω / X n ω - 1| ≤ 1 / 2 := le_of_not_gt hbad
  obtain ⟨hl, hu⟩ := abs_le.mp hr
  have hlo : (2 : ℝ)⁻¹ ≤ Y n ω / X n ω := by norm_num; linarith
  have hhi : Y n ω / X n ω ≤ 2 := by linarith
  have hLogLo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹) hlo
  rw [Real.log_inv] at hLogLo
  have hLogHi := Real.log_le_log (div_pos (hY n ω) (hX n ω)) hhi
  have hb : |Real.log (Y n ω / X n ω)| ≤ Real.log 2 := abs_le.2 ⟨hLogLo, hLogHi⟩
  have hb' : |Real.log (Y n ω) / s n - Real.log (X n ω) / s n| ≤ δ := by
    rw [← sub_div, ← Real.log_div (hY n ω).ne' (hX n ω).ne', abs_div, abs_of_pos (hs n)]
    apply (div_le_iff₀ (hs n)).2
    exact hb.trans ((div_le_iff₀ hδ).1 hn |>.trans_eq (mul_comm _ _))
  exact (not_lt_of_ge hb') hω

end Logarithms

section MarketRank

/-- The fixed-diagonal firm's rank event at an off-diagonal coordinate. -/
def offRankEvent {n : ℕ} (x : Vec n) (ij : OffIndex n) : Set (ℝ × ℝ) :=
  Iic (x ij.val.1) ×ˢ univ

theorem measurableSet_offRankEvent {n : ℕ} (x : Vec n) (ij : OffIndex n) :
    MeasurableSet (offRankEvent x ij) :=
  measurableSet_Iic.prod MeasurableSet.univ

/-- Total firm rank as a function of the split uniform scores. -/
noncomputable def splitFirmRank {n : ℕ} (w : ScoreSpace n) : ℝ :=
  (n : ℝ) + countCoordinateEvents (offRankEvent w.1.1) w.2

private theorem sum_offIndex {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ ij : OffIndex n, f ij.val.1 ij.val.2) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  classical
  have huniv : (Finset.univ : Finset (OffIndex n)) =
      (Finset.univ : Finset (PairIndex n)).subtype (fun ij ↦ ij.1 ≠ ij.2) := by
    ext ij
    simp
  rw [huniv, Finset.sum_subtype_eq_sum_filter (fun ij : PairIndex n ↦ f ij.1 ij.2),
    Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.filter_ne, Finset.sum_filter]

private theorem sum_offIndex_firm {n : ℕ} (hn : 1 ≤ n) (x : Vec n) :
    (∑ ij : OffIndex n, x ij.val.1) = ((n : ℝ) - 1) * scoreSum x := by
  rw [sum_offIndex (fun i _ ↦ x i), scoreSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]

private theorem sum_offIndex_mul_le {n : ℕ} {x y : Vec n}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    (∑ ij : OffIndex n, x ij.val.1 * y ij.val.2) ≤ scoreSum x * scoreSum y := by
  rw [sum_offIndex (fun i j ↦ x i * y j), scoreSum, scoreSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun j _ _ ↦ mul_nonneg (hx i) (hy j))

theorem measurable_splitFirmRank (n : ℕ) : Measurable (splitFirmRank (n := n)) := by
  classical
  change Measurable (fun w : ScoreSpace n ↦
    (n : ℝ) + countCoordinateEvents (offRankEvent w.1.1) w.2)
  simp only [countCoordinateEvents, Finset.sum_apply]
  apply Measurable.const_add
  refine Finset.measurable_fun_sum _ fun ij _ ↦ ?_
  have h1 : Measurable (fun w : ScoreSpace n ↦ (w.2 ij).1) := by fun_prop
  have h2 : Measurable (fun w : ScoreSpace n ↦ w.1.1 ij.val.1) := by fun_prop
  simp only [indicator, offRankEvent, mem_prod, mem_Iic, mem_univ, and_true]
  exact Measurable.ite (measurableSet_le h1 h2) measurable_const measurable_const

/-- Splitting the utilities into diagonal and off-diagonal scores preserves the rank. -/
theorem splitFirmRank_splitScores {n : ℕ} (p : Profile n) :
    splitFirmRank (splitScores n p) = (firmRankSum p : ℝ) := by
  classical
  unfold splitFirmRank
  simp only [countCoordinateEvents, Finset.sum_apply, indicator, offRankEvent, mem_prod,
    mem_Iic, mem_univ, and_true, splitScores, diagonalFirmScores, Real.exp_le_exp, neg_le_neg_iff]
  rw [sum_offIndex (fun i j ↦ if p (false, i, i) ≤ p (false, i, j) then (1 : ℝ) else 0)]
  simp only [firmRankSum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [show (n : ℝ) = ∑ _ : Fin n, (1 : ℝ) by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_comm]
  simpa using Finset.sum_erase_add Finset.univ
    (fun j : Fin n ↦ if p (false, i, i) ≤ p (false, i, j) then (1 : ℝ) else 0)
    (Finset.mem_univ i)

private theorem admissiblePairMass_pos {a x y : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - a ^ 2 * x * y := by
  have hq : a ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, pow_le_one₀ ha.1 ha.2⟩
  have hqy : a ^ 2 * y ≤ 1 := (mul_le_of_le_one_left hy.1.le hq.2).trans hy.2.le
  apply sub_pos.2
  calc
    a ^ 2 * x * y = x * (a ^ 2 * y) := by ring
    _ ≤ x * 1 := mul_le_mul_of_nonneg_left hqy hx.1.le
    _ < 1 := by simpa using hx.2

/-- The conditioned score law at one off-diagonal coordinate. -/
noncomputable def offPairConditionalMeasure {n : ℕ} (a : ℝ) (xy : Vec n × Vec n)
    (ij : OffIndex n) : Measure (ℝ × ℝ) :=
  cond pairScoreMeasure (allowedScorePair a (xy.1 ij.val.1) (xy.2 ij.val.2))

private theorem pairScoreMeasure_allowed_ne_zero {a x y : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    pairScoreMeasure (allowedScorePair a x y) ≠ 0 := by
  rw [pairScoreMeasure_allowedScorePair ha ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩,
    ← pos_iff_ne_zero, ENNReal.ofReal_pos]
  exact admissiblePairMass_pos ha hx hy

private theorem offConditional_pair_instance {n : ℕ} {a : ℝ} {xy : Vec n × Vec n}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : ∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1)
    (hy : ∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1) (ij : OffIndex n) :
    IsProbabilityMeasure (offPairConditionalMeasure a xy ij) :=
  cond_isProbabilityMeasure (pairScoreMeasure_allowed_ne_zero ha (hx _) (hy _))

private theorem offAllowedMass_ne_zero {n : ℕ} {a : ℝ} {xy : Vec n × Vec n}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : ∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1)
    (hy : ∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1) :
    offScoreMeasure n (offAllowedSet a xy) ≠ 0 := by
  rw [offScoreMeasure, offAllowedSet, Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.2 fun ij _ ↦ pairScoreMeasure_allowed_ne_zero ha (hx _) (hy _)

private theorem offConditional_pair_probability_bounds {n : ℕ} {a : ℝ} {xy : Vec n × Vec n}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : ∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1)
    (hy : ∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1) (ij : OffIndex n) :
    xy.1 ij.val.1 * (1 - a ^ 2 * xy.2 ij.val.2) ≤
        (offPairConditionalMeasure a xy ij).real (offRankEvent xy.1 ij) ∧
      (offPairConditionalMeasure a xy ij).real (offRankEvent xy.1 ij) ≤ xy.1 ij.val.1 := by
  have hx' : xy.1 ij.val.1 ∈ Icc (0 : ℝ) 1 := ⟨(hx _).1.le, (hx _).2.le⟩
  have hy' : xy.2 ij.val.2 ∈ Icc (0 : ℝ) 1 := ⟨(hy _).1.le, (hy _).2.le⟩
  have hq : a ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, pow_le_one₀ ha.1 ha.2⟩
  rw [show (offPairConditionalMeasure a xy ij).real (offRankEvent xy.1 ij) =
      (xy.1 ij.val.1 - a ^ 2 * xy.1 ij.val.1 * xy.2 ij.val.2) /
        (1 - a ^ 2 * xy.1 ij.val.1 * xy.2 ij.val.2) from
    pair_uniform_conditional_rank_mass ha hx' hy']
  exact rankIndicatorProbability_bounds hx' hy' hq (admissiblePairMass_pos ha (hx _) (hy _))

private noncomputable def offRankMean {n : ℕ} (a : ℝ) (xy : Vec n × Vec n) : ℝ :=
  ∑ ij, (offPairConditionalMeasure a xy ij).real (offRankEvent xy.1 ij)

private theorem offRankMean_bounds {n : ℕ} (hn : 1 ≤ n) {a : ℝ} {xy : Vec n × Vec n}
    (ha : a ∈ Icc (0 : ℝ) 1) (hx : ∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1)
    (hy : ∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1) :
    ((n : ℝ) - 1) * scoreSum xy.1 - a ^ 2 * scoreSum xy.1 * scoreSum xy.2 ≤
        offRankMean a xy ∧
      offRankMean a xy ≤ ((n : ℝ) - 1) * scoreSum xy.1 := by
  constructor
  · have hmul := mul_le_mul_of_nonneg_left
      (sum_offIndex_mul_le (fun i ↦ (hx i).1.le) (fun i ↦ (hy i).1.le)) (sq_nonneg a)
    calc
      _ ≤ ((n : ℝ) - 1) * scoreSum xy.1 -
          a ^ 2 * (∑ ij : OffIndex n, xy.1 ij.val.1 * xy.2 ij.val.2) := by
        linarith only [hmul]
      _ = ∑ ij : OffIndex n, xy.1 ij.val.1 * (1 - a ^ 2 * xy.2 ij.val.2) := by
        rw [← sum_offIndex_firm hn, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ _ := Finset.sum_le_sum fun ij _ ↦ (offConditional_pair_probability_bounds ha hx hy ij).1
  · rw [← sum_offIndex_firm hn]
    exact Finset.sum_le_sum fun ij _ ↦ (offConditional_pair_probability_bounds ha hx hy ij).2

private theorem offRankMean_normalized_bias {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    {xy : Vec n × Vec n} (ha : a ∈ Icc (0 : ℝ) 1)
    (hx : ∀ i, xy.1 i ∈ Ioo (0 : ℝ) 1) (hy : ∀ i, xy.2 i ∈ Ioo (0 : ℝ) 1)
    (hX : 0 < scoreSum xy.1) :
    |((n : ℝ) + offRankMean a xy) / ((n : ℝ) * scoreSum xy.1) - 1|
      ≤ 1 / scoreSum xy.1 + 1 / (n : ℝ) + a ^ 2 * scoreSum xy.2 / (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hY : 0 ≤ scoreSum xy.2 := Finset.sum_nonneg fun i _ ↦ (hy i).1.le
  have hden := mul_pos hn' hX
  have hb := offRankMean_bounds hn ha hx hy
  have H :
      ((n : ℝ) + offRankMean a xy) / ((n : ℝ) * scoreSum xy.1) - 1 =
        ((n : ℝ) + offRankMean a xy - (n : ℝ) * scoreSum xy.1) /
          ((n : ℝ) * scoreSum xy.1) := by
    field_simp
  rw [H, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have H' :
      (1 / scoreSum xy.1 + 1 / (n : ℝ) + a ^ 2 * scoreSum xy.2 / (n : ℝ)) *
          ((n : ℝ) * scoreSum xy.1) =
        (n : ℝ) + scoreSum xy.1 + a ^ 2 * scoreSum xy.1 * scoreSum xy.2 := by
    field_simp
  rw [H']
  apply abs_le.2
  constructor <;>
    nlinarith only [hb.1, hb.2, hX.le, hn'.le, mul_nonneg (mul_nonneg (sq_nonneg a) hX.le) hY]

private theorem offConditional_scoreRank_deviation_le {n : ℕ} (hn : 1 ≤ n) {a η : ℝ}
    (ha : a ∈ Icc 0 1) (hη : 0 < η) {xy : Vec n × Vec n}
    (hx : ∀ i, xy.1 i ∈ Ioo 0 1) (hy : ∀ i, xy.2 i ∈ Ioo 0 1)
    (hX : 1 ≤ scoreSum xy.1)
    (hBias : 1 / scoreSum xy.1 + 1 / (n : ℝ) +
      a ^ 2 * scoreSum xy.2 / (n : ℝ) ≤ η / 2) :
    (cond (offScoreMeasure n) (offAllowedSet a xy)).real
      {z | η < |splitFirmRank (xy, z) / ((n : ℝ) * scoreSum xy.1) - 1|}
      ≤ 4 / (η ^ 2 * (n : ℝ)) := by
  classical
  let X := scoreSum xy.1
  let A := offRankEvent xy.1
  let ν := offPairConditionalMeasure a xy
  let mean := offRankMean a xy
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * X := mul_pos hn' hXp
  have hr : 0 < η / 2 * ((n : ℝ) * X) := mul_pos (by positivity) hden
  have hbias := (offRankMean_normalized_bias hn ha hx hy hXp).trans hBias
  have hmean : mean ≤ (n : ℝ) * X := by
    exact (offRankMean_bounds hn ha hx hy).2.trans (mul_le_mul_of_nonneg_right (by linarith) hXp.le)
  let (ij : OffIndex n) : IsProbabilityMeasure (ν ij) :=
    offConditional_pair_instance ha hx hy ij
  have hbox : cond (offScoreMeasure n) (offAllowedSet a xy) = Measure.pi ν := by
    unfold offScoreMeasure offAllowedSet ν offPairConditionalMeasure
    exact cond_pi_box (fun _ ↦ pairScoreMeasure) _
      (fun ij ↦ pairScoreMeasure_allowed_ne_zero ha (hx ij.val.1) (hy ij.val.2))
  rw [hbox]
  have hsub : {z | η < |splitFirmRank (xy, z) / ((n : ℝ) * X) - 1|}
      ⊆ {z | η / 2 * ((n : ℝ) * X) ≤ |countCoordinateEvents A z - mean|} := by
    intro z hz
    change η < |splitFirmRank (xy, z) / ((n : ℝ) * X) - 1| at hz
    change η / 2 * ((n : ℝ) * X) ≤ |countCoordinateEvents A z - mean|
    have heq : splitFirmRank (xy, z) / ((n : ℝ) * X) - 1 =
        (countCoordinateEvents A z - mean) / ((n : ℝ) * X) +
          (((n : ℝ) + mean) / ((n : ℝ) * X) - 1) := by
      change ((n : ℝ) + countCoordinateEvents A z) / ((n : ℝ) * X) - 1 = _
      simp only [div_eq_mul_inv]
      ring
    rw [heq] at hz
    have hTriangle := abs_add_le ((countCoordinateEvents A z - mean) / ((n : ℝ) * X))
      (((n : ℝ) + mean) / ((n : ℝ) * X) - 1)
    have hstep : η / 2 < |(countCoordinateEvents A z - mean) / ((n : ℝ) * X)| :=
      by linarith only [hz, hTriangle, show |((n : ℝ) + mean) / ((n : ℝ) * X) - 1| ≤ η / 2 from hbias]
    rw [abs_div, abs_of_pos hden, lt_div_iff₀ hden] at hstep
    exact hstep.le
  calc
    _ ≤ (Measure.pi ν).real
        {z | η / 2 * ((n : ℝ) * X) ≤ |countCoordinateEvents A z - mean|} :=
      measureReal_mono hsub
    _ ≤ mean / (η / 2 * ((n : ℝ) * X)) ^ 2 :=
      measureReal_countCoordinateEvents_deviation_le ν A (measurableSet_offRankEvent _) hr
    _ ≤ ((n : ℝ) * X) / (η / 2 * ((n : ℝ) * X)) ^ 2 :=
      div_le_div_of_nonneg_right hmean (sq_nonneg _)
    _ = 4 / (η ^ 2 * (n : ℝ) * X) := by
      field_simp
      norm_num
    _ ≤ 4 / (η ^ 2 * (n : ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact le_mul_of_one_le_right (by positivity) hX

/-- Uniform Chebyshev bound on one diagonal fiber whose score sum and conditional bias are
controlled. The probability bound is stated for the unnormalized restriction used in Fubini. -/
theorem offRestricted_scoreRank_deviation_le {n : ℕ} (hn : 1 ≤ n) {a η : ℝ}
    (ha : a ∈ Icc 0 1) (hη : 0 < η) {xy : Vec n × Vec n}
    (hx : ∀ i, xy.1 i ∈ Ioo 0 1) (hy : ∀ i, xy.2 i ∈ Ioo 0 1)
    (hX : 1 ≤ scoreSum xy.1)
    (hBias : 1 / scoreSum xy.1 + 1 / (n : ℝ) +
      a ^ 2 * scoreSum xy.2 / (n : ℝ) ≤ η / 2) :
    offRestrictedScoreMeasure a xy
      {z | η < |splitFirmRank (xy, z) / ((n : ℝ) * scoreSum xy.1) - 1|}
      ≤ ENNReal.ofReal (4 / (η ^ 2 * (n : ℝ))) * offRestrictedScoreMeasure a xy univ := by
  let B : Set (OffIndex n → ℝ × ℝ) :=
    {z | η < |splitFirmRank (xy, z) / ((n : ℝ) * scoreSum xy.1) - 1|}
  have hB : MeasurableSet B := by
    apply measurableSet_lt measurable_const
    have hsplit := (measurable_splitFirmRank n).comp (measurable_prodMk_left (x := xy))
    exact ((hsplit.div_const _).sub_const _).abs
  let S := offAllowedSet a xy
  let μ := offScoreMeasure n
  have hS : μ S ≠ 0 := offAllowedMass_ne_zero ha hx hy
  have hμSt : μ S ≠ ⊤ := measure_ne_top _ _
  let := cond_isProbabilityMeasure hS
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbNonneg : 0 ≤ 4 / (η ^ 2 * (n : ℝ)) := by positivity
  have hprob : cond μ S B ≤ ENNReal.ofReal (4 / (η ^ 2 * (n : ℝ))) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hbNonneg).2
      (offConditional_scoreRank_deviation_le hn ha hη hx hy hX hBias)
  have hcancel : μ (B ∩ S) = cond μ S B * μ S := by
    rw [cond_apply' hB, inter_comm S B, mul_comm (μ S)⁻¹ _, mul_assoc,
      ENNReal.inv_mul_cancel hS hμSt, mul_one]
  change offRestrictedScoreMeasure a xy B ≤ _
  rw [offRestrictedScoreMeasure_eq, Measure.restrict_apply hB, Measure.restrict_apply_univ]
  exact hcancel.le.trans (mul_le_mul_of_nonneg_right hprob bot_le)

end MarketRank

end SupercriticalLogRank
