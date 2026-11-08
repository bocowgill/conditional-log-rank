module

public import Mathlib

@[expose] public section

/-!
# Tail consequences of the score law

An interior logarithmic CDF limit controls both the lower tail at fixed score
and the upper tail at scores proportional to the market size.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace SupercriticalLogRank

private theorem tendsto_marketSize : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)

/-- The CDF event on the logarithmic scale is the score cutoff event almost everywhere. -/
theorem measureReal_logScore_eq_power {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : ∀ᵐ ω ∂μ, 0 < X ω) {n t : ℝ} (hn : 1 < n) :
    μ.real {ω | Real.log (X ω) / Real.log n ≤ t} = μ.real {ω | X ω ≤ n ^ t} := by
  apply measureReal_congr
  filter_upwards [hX] with ω hω
  apply propext
  rw [div_le_iff₀ (Real.log_pos hn), Real.le_rpow_iff_log_le hω (zero_lt_one.trans hn)]

section VaryingSpace

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
variable (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]

/-- The uniform interior score law makes every fixed lower tail vanish. -/
theorem tendsto_measureReal_score_le_const (X : ∀ k, Ω k → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Ico 0 1)
    (hX : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ (μ k).real {ω | X k ω ≤ ((k + 2 : ℕ) : ℝ) ^ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ)))) (C : ℝ) :
    Tendsto (fun k ↦ (μ k).real {ω | X k ω ≤ C}) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun l hl ↦ Eventually.of_forall fun _ ↦
    hl.trans_le measureReal_nonneg, ?_⟩
  intro u hu
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ.2
  let δ := min ((1 - ρ) / 2) (u * (1 - ρ) / 2)
  have hδ : 0 < δ := lt_min (half_pos hden) (half_pos (mul_pos hu hden))
  have hδ₁ : δ ≤ (1 - ρ) / 2 := min_le_left _ _
  have hδ₂ : δ ≤ u * (1 - ρ) / 2 := min_le_right _ _
  have ht : ρ + δ ∈ Ioo ρ 1 := ⟨by linarith, by linarith⟩
  have ht₀ : 0 < ρ + δ := add_pos_of_nonneg_of_pos hρ.1 hδ
  have hlt : (ρ + δ - ρ) / (1 - ρ) < u := by
    apply (div_lt_iff₀ hden).2
    linarith [mul_pos hu hden]
  have hC : ∀ᶠ k : ℕ in atTop, C ≤ ((k + 2 : ℕ) : ℝ) ^ (ρ + δ) :=
    (tendsto_rpow_atTop ht₀ |>.comp tendsto_marketSize).eventually (eventually_ge_atTop C)
  filter_upwards [hC, (tendsto_order.1 (hX (ρ + δ) ht)).2 u hlt] with k hk hupper
  exact (measureReal_mono (fun ω hω ↦ (show X k ω ≤ C from hω).trans hk)).trans_lt hupper

/-- The same interior score law makes all upper tails at a fixed fraction of the
market size vanish. -/
theorem tendsto_measureReal_score_over_size_tail (Y : ∀ k, Ω k → ℝ)
    (hYmeas : ∀ k, Measurable (Y k)) {ρ : ℝ} (hρ : ρ ∈ Ico 0 1)
    (hY : ∀ t ∈ Ioo ρ 1,
      Tendsto (fun k : ℕ ↦ (μ k).real {ω | Y k ω ≤ ((k + 2 : ℕ) : ℝ) ^ t})
        atTop (𝓝 ((t - ρ) / (1 - ρ)))) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k ↦ (μ k).real {ω | c < Y k ω / ((k + 2 : ℕ) : ℝ)}) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun l hl ↦ Eventually.of_forall fun _ ↦
    hl.trans_le measureReal_nonneg, ?_⟩
  intro u hu
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ.2
  let δ := min ((1 - ρ) / 2) (u * (1 - ρ) / 2)
  have hδ : 0 < δ := lt_min (half_pos hden) (half_pos (mul_pos hu hden))
  have hδ₁ : δ ≤ (1 - ρ) / 2 := min_le_left _ _
  have hδ₂ : δ ≤ u * (1 - ρ) / 2 := min_le_right _ _
  have ht : 1 - δ ∈ Ioo ρ 1 := ⟨by linarith, by linarith⟩
  have hlt : 1 - (1 - δ - ρ) / (1 - ρ) < u := by
    have hcalc : 1 - (1 - δ - ρ) / (1 - ρ) = δ / (1 - ρ) := by
      field_simp
      ring
    rw [hcalc]
    apply (div_lt_iff₀ hden).2
    linarith [mul_pos hu hden]
  have hTail : ∀ᶠ k : ℕ in atTop,
      ((k + 2 : ℕ) : ℝ) ^ (1 - δ) / ((k + 2 : ℕ) : ℝ) < c := by
    filter_upwards [(tendsto_rpow_neg_atTop hδ |>.comp tendsto_marketSize).eventually
      (gt_mem_nhds hc)] with k hk
    have hn : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
    rw [← Real.rpow_sub_one hn.ne', show 1 - δ - 1 = -δ by ring]
    exact hk
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub (hY (1 - δ) ht)
  filter_upwards [hTail, (tendsto_order.1 hlim).2 u hlt] with k hk hupper
  have hn : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
  have hsubset : {ω | c < Y k ω / ((k + 2 : ℕ) : ℝ)} ⊆
      {ω | Y k ω ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ)}ᶜ := by
    intro ω hω
    change ¬ Y k ω ≤ _
    intro hle
    exact (not_lt_of_ge (div_le_div_of_nonneg_right hle hn.le))
      (hk.trans (show c < Y k ω / ((k + 2 : ℕ) : ℝ) from hω))
  have hmeas : MeasurableSet {ω | Y k ω ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ)} :=
    measurableSet_le (hYmeas k) measurable_const
  calc
    _ ≤ (μ k).real {ω | Y k ω ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ)}ᶜ := measureReal_mono hsubset
    _ = 1 - (μ k).real {ω | Y k ω ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ)} := by
      rw [measureReal_compl hmeas, probReal_univ]
    _ < u := hupper

end VaryingSpace

end SupercriticalLogRank
