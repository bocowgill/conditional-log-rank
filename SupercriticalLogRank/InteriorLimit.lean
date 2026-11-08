module

public import SupercriticalLogRank.SimplexConcentration
public import SupercriticalLogRank.GlobalBound
public import SupercriticalLogRank.Scales

@[expose] public section

/-! Uniform convergence of the simplex average on interior score windows. -/

namespace SupercriticalLogRank

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- The two estimates for simplex typicality convert uniform pointwise convergence on
typical vectors to uniform convergence of the integral on the same windows. -/
theorem eventually_radialDensity_uniform_of_logTaylor
    (q : ℕ → ℝ) (window : ℕ → Set ℝ)
    (hq : ∀ᶠ k in atTop, q k ∈ Ioc (0 : ℝ) 1)
    (hpos : ∀ᶠ k in atTop, ∀ s ∈ window k, 0 < s)
    (htaylor : ∀ α > 0, ∀ᶠ k in atTop, ∀ s ∈ window k,
      ∀ u ∈ simplexTypical (k + 2) (α / 2),
        0 < radialWeight (k + 2) (q k) s u ∧
        |Real.log (radialWeight (k + 2) (q k) s u) -
            (1 - (↑(k + 2) : ℝ) * ∑ i, (u i) ^ 2)| < α / 2)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ s ∈ window k,
      |radialDensity (k + 2) (q k) s - Real.exp (-1)| ≤ η := by
  obtain ⟨α, hα, hαclose⟩ := (Metric.continuousAt_iff.mp
    (Real.continuous_exp.continuousAt (x := (-1 : ℝ)))) (η / 2) (by positivity)
  have htail : Tendsto
      (fun k : ℕ ↦ (Real.exp 2 + Real.exp (-1)) *
        (simplexLaw (k + 2)).real (simplexTypical (k + 2) (α / 2))ᶜ) atTop (𝓝 0) := by
    have h := (tendsto_simplexLaw_typical_compl (η := α / 2) (by positivity)).comp
      (tendsto_add_atTop_nat 2)
    simpa using h.const_mul (Real.exp 2 + Real.exp (-1))
  have htail' : ∀ᶠ k in atTop, (Real.exp 2 + Real.exp (-1)) *
      (simplexLaw (k + 2)).real (simplexTypical (k + 2) (α / 2))ᶜ ≤ η / 2 :=
    (htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 2))).mono
      (fun _ h ↦ h.le)
  filter_upwards [hq, hpos, htaylor α hα, htail'] with k hqk hposk htk htailk
  intro s hs
  have hSimplex : ∀ᵐ u ∂simplexLaw (k + 2),
      (∀ i, 0 ≤ u i) ∧ scoreSum u = 1 := by
    filter_upwards [ae_simplexLaw (k + 2) (by omega)] with u hu
    exact ⟨fun i ↦ (hu.1 i).le, hu.2⟩
  refine (abs_radialDensity_sub_exp_neg_one_le (η := η / 2) hqk (hposk s hs) (by positivity) hSimplex
    (measurableSet_simplexTypical (k + 2) (α / 2)) ?_).trans (by linarith)
  intro u hu
  obtain ⟨hw, hwclose⟩ := htk s hs u hu
  have hQ : |(↑(k + 2) : ℝ) * (∑ i, (u i) ^ 2) - 2| < α / 2 := hu.2.2
  have hdist : dist (Real.log (radialWeight (k + 2) (q k) s u)) (-1) < α := by
    rw [Real.dist_eq]
    have ht := abs_add_le
      (Real.log (radialWeight (k + 2) (q k) s u) - (1 - (↑(k + 2) : ℝ) * ∑ i, (u i) ^ 2))
      (-((↑(k + 2) : ℝ) * (∑ i, (u i) ^ 2) - 2))
    rw [abs_neg] at ht
    have heq : Real.log (radialWeight (k + 2) (q k) s u) - (-1) =
        (Real.log (radialWeight (k + 2) (q k) s u) -
          (1 - (↑(k + 2) : ℝ) * ∑ i, (u i) ^ 2)) +
          (-((↑(k + 2) : ℝ) * (∑ i, (u i) ^ 2) - 2)) := by ring
    rw [heq]
    linarith
  have hclose := hαclose hdist
  rw [Real.dist_eq, Real.exp_log hw] at hclose
  exact hclose.le

/-- The simplex average tends uniformly to $e^{-1}$ on the interior radial window. -/
theorem eventually_radialDensity_interior_of_scales
    (q : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hq : ∀ n, q n ∈ Ioc (0 : ℝ) 1)
    (hsmall : ∀ᶠ k : ℕ in atTop,
      let N : ℝ := ((k + 2 : ℕ) : ℝ)
      let M := taylorM N
      let L := taylorL N
      M ≤ 1 / 2 ∧ M * (1 + L) ^ 3 ≤ 1 / 4 ∧ M + columnError M L ≤ 1 / 2)
    (herror : Tendsto (fun k : ℕ ↦
      let N : ℝ := ((k + 2 : ℕ) : ℝ)
      let M := taylorM N
      let L := taylorL N
      N * (columnError M L + 2 * (M + columnError M L) ^ 2)) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℝ,
      ((k + 2 : ℕ) : ℝ) ^ δ / q k ≤ s →
      s ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ) →
      |radialDensity (k + 2) (q k) s - Real.exp (-1)| < η := by
  let window (k : ℕ) :=
    Icc (((k + 2 : ℕ) : ℝ) ^ δ / q k) (((k + 2 : ℕ) : ℝ) ^ (1 - δ))
  have hpos : ∀ᶠ k in atTop, ∀ s ∈ window k, 0 < s := by
    refine .of_forall fun k s hs ↦ ?_
    exact (div_pos (Real.rpow_pos_of_pos (by positivity) _) (hq k).1).trans_le hs.1
  have hTaylor (α : ℝ) (hα : 0 < α) :
      ∀ᶠ k in atTop, ∀ s ∈ window k, ∀ u ∈ simplexTypical (k + 2) (α / 2),
        0 < radialWeight (k + 2) (q k) s u ∧
          |Real.log (radialWeight (k + 2) (q k) s u) -
            (1 - (↑(k + 2) : ℝ) * ∑ i, (u i) ^ 2)| < α / 2 := by
    have hError := herror.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < α / 2))
    filter_upwards [hsmall, hError, eventually_taylorWindow hδ] with k hsk hek hwk
    intro s hs u hu
    have hu0 (i : Fin (k + 2)) : 0 ≤ u i := (hu.1.1 i).le
    have huM (i : Fin (k + 2)) : u i ≤ taylorM ((k + 2 : ℕ) : ℝ) := hu.2.1 i
    obtain ⟨hM, hL, hLq, hcube, hcap⟩ :=
      hwk (q k) s u (hq k).1 (hq k).2 hs.1 hs.2 hu0 huM
    obtain ⟨hp, hb⟩ := abs_log_radialWeight_sub_le hu0 huM hM hsk.1 hu.1.2
      hL hLq hsk.2.1 hcap hsk.2.2 hcube
    exact ⟨hp, hb.trans_lt hek⟩
  filter_upwards [eventually_radialDensity_uniform_of_logTaylor q window
    (.of_forall hq) hpos hTaylor (η := η / 2) (by positivity)] with k hk
  intro s hlo hhi
  exact (hk s ⟨hlo, hhi⟩).trans_lt (by linarith)

/-- The interior window estimate for the model's logarithmic truncation scales. -/
theorem eventually_radialDensity_interior
    (q : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hq : ∀ n, q n ∈ Ioc (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℝ,
      ((k + 2 : ℕ) : ℝ) ^ δ / q k ≤ s →
      s ≤ ((k + 2 : ℕ) : ℝ) ^ (1 - δ) →
      |radialDensity (k + 2) (q k) s - Real.exp (-1)| < η :=
  eventually_radialDensity_interior_of_scales q δ hδ hq eventually_taylorSmall
    tendsto_rankSize_taylorTotalError η hη

end SupercriticalLogRank
