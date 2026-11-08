module

public import SupercriticalLogRank.MarketBasics

@[expose] public section

/-! Integrating the worker diagonal scores separates the stability kernel into columns. -/

namespace SupercriticalLogRank

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measurableSet_cube (n : ℕ) : MeasurableSet (cube n) := by
  exact MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Icc

theorem stabilityKernel_columns {n : ℕ} (q : ℝ) (x y : Vec n) :
    stabilityKernel q x y = ∏ j, ∏ i ∈ Finset.univ.erase j, (1 - q * x i * y j) := by
  unfold stabilityKernel
  simp_rw [← Finset.filter_ne', Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases h : i = j <;> simp [h, Ne.symm]

theorem stabilityKernel_swap {n : ℕ} (q : ℝ) (x y : Vec n) :
    stabilityKernel q x y = stabilityKernel q y x := by
  rw [stabilityKernel_columns]
  unfold stabilityKernel
  refine Finset.prod_congr rfl fun _ _ ↦ Finset.prod_congr rfl fun _ _ ↦ ?_
  ring

theorem integral_stabilityKernel_columns {n : ℕ} (q : ℝ) (x : Vec n) :
    (∫ y in cube n, stabilityKernel q x y) =
      ∏ j, ∫ y in (0 : ℝ)..1, ∏ i ∈ Finset.univ.erase j, (1 - q * x i * y) := by
  simp_rw [stabilityKernel_columns]
  rw [cube, volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod
    (fun (j : Fin n) (y : ℝ) ↦ ∏ i ∈ Finset.univ.erase j, (1 - q * x i * y))]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem integral_stabilityKernel_radial {n : ℕ} {q s : ℝ} (hqs : q * s ≠ 0) (u : Vec n) :
    (∫ y in cube n, stabilityKernel q (s • u) y) =
      (q * s)⁻¹ ^ n * ∏ j, columnIntegral q s u j := by
  have hprod : (∏ _j : Fin n, (q * s)⁻¹) = (q * s)⁻¹ ^ n := by simp
  rw [integral_stabilityKernel_columns, ← hprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hs := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := fun z : ℝ ↦ ∏ i ∈ Finset.univ.erase j, (1 - u i * z)) hqs
  calc
    (∫ y in (0 : ℝ)..1, ∏ i ∈ Finset.univ.erase j, (1 - q * (s • u) i * y)) =
        ∫ y in (0 : ℝ)..1, ∏ i ∈ Finset.univ.erase j, (1 - u i * (q * s * y)) := by
      congr 1
      ext y
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      simpa only [columnIntegral, mul_zero, mul_one, smul_eq_mul] using hs

end

end SupercriticalLogRank
