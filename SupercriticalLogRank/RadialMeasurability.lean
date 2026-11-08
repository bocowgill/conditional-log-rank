module

public import SupercriticalLogRank.MarketBasics

@[expose] public section

/-! Joint measurability of the radial column integrals and their simplex average. -/

namespace SupercriticalLogRank

open MeasureTheory Set

noncomputable section

private theorem measurable_columnIntegrand {n : ℕ} (j : Fin n) :
    Measurable (fun p : (ℝ × Vec n) × ℝ ↦
      ∏ i ∈ Finset.univ.erase j, (1 - p.1.2 i * p.2)) := by
  fun_prop (disch := exact measurable_pi_apply _)

theorem measurable_columnIntegral {n : ℕ} (q : ℝ) (j : Fin n) :
    Measurable (fun p : ℝ × Vec n ↦ columnIntegral q p.1 p.2 j) := by
  classical
  let f : (ℝ × Vec n) × ℝ → ℝ :=
    fun p ↦ ∏ i ∈ Finset.univ.erase j, (1 - p.1.2 i * p.2)
  have hf : Measurable f := measurable_columnIntegrand j
  have h₁ : MeasurableSet {p : (ℝ × Vec n) × ℝ | 0 < p.2 ∧ p.2 ≤ q * p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.mul measurable_fst.fst))
  have h₂ : MeasurableSet {p : (ℝ × Vec n) × ℝ | q * p.1.1 < p.2 ∧ p.2 ≤ 0} :=
    (measurableSet_lt (measurable_const.mul measurable_fst.fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have ha := (hf.indicator h₁).stronglyMeasurable.integral_prod_right' (ν := volume)
  have hb := (hf.indicator h₂).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert ha.measurable.sub hb.measurable using 1
  ext p
  simp only [columnIntegral, intervalIntegral, ← integral_indicator measurableSet_Ioc]
  rfl

theorem measurable_radialWeight (n : ℕ) (q : ℝ) :
    Measurable (fun p : ℝ × Vec n ↦ radialWeight n q p.1 p.2) := by
  classical
  have hc : MeasurableSet (cube n) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Icc
  have hm : Measurable (fun p : ℝ × Vec n ↦ p.1 • p.2) :=
    measurable_fst.smul measurable_snd
  exact (Finset.measurable_fun_prod _ fun j _ ↦ measurable_columnIntegral q j).ite
    (hc.preimage hm) measurable_const

theorem measurable_radialDensity (n : ℕ) (q : ℝ) : Measurable (radialDensity n q) :=
  (measurable_radialWeight n q).stronglyMeasurable.integral_prod_right'.measurable

end

end SupercriticalLogRank
