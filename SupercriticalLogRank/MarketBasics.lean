module

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import SupercriticalLogRank.Model

@[expose] public section

/-! Measurability and normalization of the conditional market. -/

namespace SupercriticalLogRank

open MeasureTheory Set
open ProbabilityTheory (cdf_eq_real cdf_expMeasure_eq expMeasure isProbabilityMeasure_expMeasure)
open scoped ENNReal

instance (n : ℕ) : IsProbabilityMeasure (marketMeasure n) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  unfold marketMeasure
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (expVectorMeasure n) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  unfold expVectorMeasure
  infer_instance

theorem measurable_scoreSum (n : ℕ) : Measurable (scoreSum (n := n)) := by
  unfold scoreSum
  fun_prop

theorem measurable_simplexNormalize (n : ℕ) :
    Measurable (fun e : Vec n ↦ fun i ↦ e i / scoreSum e) :=
  Measurable.of_eval fun i ↦ (measurable_pi_apply i).div (measurable_scoreSum n)

instance (n : ℕ) : IsProbabilityMeasure (simplexLaw n) := by
  unfold simplexLaw
  exact inferInstance

theorem measurableSet_stableEvent (n : ℕ) (ε : ℝ) : MeasurableSet (stableEvent n ε) := by
  apply Measurable.setOf
  fun_prop (disch := exact measurable_pi_apply _)

theorem measurable_firmRankSum (n : ℕ) : Measurable (firmRankSum (n := n)) := by
  classical
  unfold firmRankSum
  exact Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun j _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
      measurable_const measurable_const

theorem measurableSet_rankCutoffEvent (n : ℕ) (t : ℝ) : MeasurableSet (rankCutoffEvent n t) := by
  apply Measurable.setOf
  exact (Measurable.of_discrete (f := fun r : ℕ ↦ (r : ℝ) ≤ (n : ℝ) ^ (1 + t))).comp
    (measurable_firmRankSum n)

theorem marketMeasure_real_stable_pos (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 < (marketMeasure n).real (stableEvent n ε) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  have hInterval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
      0 < (expMeasure 1).real (Ioc a b) := by
    rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.2 hab.le) measurableSet_Iic,
      ← cdf_eq_real, ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, cdf_expMeasure_eq zero_lt_one]
    simp only [ite_eq_left ha, ite_eq_left (ha.trans hab.le), one_mul]
    linarith [Real.exp_lt_exp.mpr (neg_lt_neg hab)]
  let intervals (ij : Bool × Fin n × Fin n) : Set ℝ :=
    if ij.1 = true then univ else if ij.2.1 = ij.2.2 then Ioc 2 3 else Ioc 0 1
  have hsub : pi univ intervals ⊆ stableEvent n ε := by
    intro p hp i j hne hblock
    have hdiag := hp (false, i, i) (mem_univ _)
    have hij := hp (false, i, j) (mem_univ _)
    simp [intervals] at hdiag
    simp [intervals, hne] at hij
    linarith [hdiag.1, hij.2, hblock.1]
  refine lt_of_lt_of_le ?_ (measureReal_mono hsub)
  unfold marketMeasure
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_pos fun ij _ ↦ ?_
  change 0 < (expMeasure 1).real (intervals ij)
  dsimp [intervals]
  split_ifs
  · simp
  · exact hInterval (by norm_num) (by norm_num)
  · exact hInterval (by norm_num) (by norm_num)

theorem conditionedMarket_isProbability (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsProbabilityMeasure (conditionedMarket n ε) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  exact (measureReal_ne_zero_iff).mp (marketMeasure_real_stable_pos n hε).ne'

theorem conditionedMarket_real (n : ℕ) (ε : ℝ) (A : Set (Profile n)) :
    (conditionedMarket n ε).real A =
      (marketMeasure n).real (stableEvent n ε ∩ A) / (marketMeasure n).real (stableEvent n ε) := by
  rw [conditionedMarket, measureReal_def,
    ProbabilityTheory.cond_apply (measurableSet_stableEvent n ε)]
  simp [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

theorem conditionedMarket_real_rankCutoff (n : ℕ) (ε t : ℝ) :
    (conditionedMarket n ε).real (rankCutoffEvent n t) = conditionalRankProbability n ε t :=
  conditionedMarket_real n ε (rankCutoffEvent n t)

end SupercriticalLogRank
