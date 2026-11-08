module

public import SupercriticalLogRank.RadialMeasurability

@[expose] public section

/-! Uniform bounds for the radial integrand, including the short-radius estimate. -/

namespace SupercriticalLogRank

open MeasureTheory Set
open scoped BigOperators

variable {n : ℕ}

private theorem coordinate_mul_mem_Icc {q s z : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hz : z ∈ Icc 0 (q * s)) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (i : Fin n) :
    u i * z ∈ Icc 0 1 := by
  have hi : s * u i ∈ Icc (0 : ℝ) 1 := hcube i (mem_univ i)
  refine ⟨mul_nonneg (hu i) hz.1, ?_⟩
  calc
    u i * z ≤ u i * (q * s) := mul_le_mul_of_nonneg_left hz.2 (hu i)
    _ = q * (s * u i) := by ring
    _ ≤ s * u i := mul_le_of_le_one_left hi.1 hq
    _ ≤ 1 := hi.2

private theorem continuous_columnIntegrand (u : Vec n) (j : Fin n) :
    Continuous (fun z : ℝ ↦ ∏ i ∈ Finset.univ.erase j, (1 - u i * z)) := by
  fun_prop

private theorem columnIntegrand_mem_Icc {q s z : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hz : z ∈ Icc 0 (q * s)) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (j : Fin n) :
    (∏ i ∈ Finset.univ.erase j, (1 - u i * z)) ∈ Icc (0 : ℝ) 1 := by
  have h := coordinate_mul_mem_Icc hq hz hu hcube
  refine ⟨Finset.prod_nonneg (fun i _ ↦ sub_nonneg.mpr (h i).2), ?_⟩
  calc
    _ ≤ ∏ _i ∈ Finset.univ.erase j, (1 : ℝ) := by
      exact Finset.prod_le_prod₀ (fun i _ ↦ sub_nonneg.mpr (h i).2)
        (fun i _ ↦ sub_le_self 1 (h i).1)
    _ = 1 := by simp

theorem columnIntegral_nonneg {q s : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hqs : 0 ≤ q * s) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (j : Fin n) :
    0 ≤ columnIntegral q s u j :=
  intervalIntegral.integral_nonneg hqs
    (fun _ hz ↦ (columnIntegrand_mem_Icc hq hz hu hcube j).1)

theorem columnIntegral_le_length {q s : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hqs : 0 ≤ q * s) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (j : Fin n) :
    columnIntegral q s u j ≤ q * s := by
  unfold columnIntegral
  calc
    _ ≤ ∫ _z in (0 : ℝ)..(q * s), (1 : ℝ) :=
      intervalIntegral.integral_mono_on hqs ((continuous_columnIntegrand u j).intervalIntegrable 0 (q * s))
        (continuous_const.intervalIntegrable 0 (q * s))
        (fun _ hz ↦ (columnIntegrand_mem_Icc hq hz hu hcube j).2)
    _ = q * s := by simp

theorem columnIntegrand_le_exp {q s z : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hz : z ∈ Icc 0 (q * s)) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (hus : scoreSum u = 1) (j : Fin n) :
    (∏ i ∈ Finset.univ.erase j, (1 - u i * z)) ≤ Real.exp (-(1 - u j) * z) := by
  have h := coordinate_mul_mem_Icc hq hz hu hcube
  have hsum : (∑ i ∈ Finset.univ.erase j, u i) = 1 - u j := by
    have heq := Finset.sum_erase_add Finset.univ u (Finset.mem_univ j)
    change (∑ i ∈ Finset.univ.erase j, u i) + u j = scoreSum u at heq
    linarith
  calc
    _ ≤ ∏ i ∈ Finset.univ.erase j, Real.exp (-(u i * z)) :=
      Finset.prod_le_prod₀ (fun i _ ↦ sub_nonneg.mpr (h i).2)
        (fun i _ ↦ by simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(u i * z)))
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_mul, hsum, neg_mul]

private theorem integral_exp_neg_mul (d : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ z in (0 : ℝ)..d, Real.exp (-c * z)) = (1 - Real.exp (-c * d)) / c := by
  have h := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := d) (f := Real.exp) (-c)
  rw [mul_zero, integral_exp, Real.exp_zero] at h
  apply (eq_div_iff (ne_of_gt hc)).2
  linarith

private theorem columnIntegral_le_exp_of_two_le {q s : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hqs : 0 ≤ q * s) (hs : 2 ≤ s) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (hus : scoreSum u = 1) (j : Fin n) :
    columnIntegral q s u j ≤ Real.exp (2 * u j) := by
  have hj : s * u j ≤ 1 := (hcube j (mem_univ j)).2
  have hhalf : u j ≤ 1 / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (hu j)]
  have hpos : 0 < 1 - u j := by linarith
  unfold columnIntegral
  calc
    _ ≤ ∫ z in (0 : ℝ)..(q * s), Real.exp (-(1 - u j) * z) :=
      intervalIntegral.integral_mono_on hqs ((continuous_columnIntegrand u j).intervalIntegrable 0 (q * s))
        ((show Continuous (fun z : ℝ ↦ Real.exp (-(1 - u j) * z)) by fun_prop).intervalIntegrable 0 (q * s))
        (fun _ hz ↦ columnIntegrand_le_exp hq hz hu hcube hus j)
    _ = (1 - Real.exp (-(1 - u j) * (q * s))) / (1 - u j) :=
      integral_exp_neg_mul (q * s) hpos
    _ ≤ 1 / (1 - u j) := by
      gcongr
      exact sub_le_self _ (Real.exp_nonneg _)
    _ ≤ 2 * u j + 1 := by
      apply (div_le_iff₀ hpos).2
      nlinarith [mul_nonneg (hu j) (sub_nonneg.mpr (show 2 * u j ≤ 1 by linarith))]
    _ ≤ Real.exp (2 * u j) := Real.add_one_le_exp _

private theorem columnIntegral_le_exp_of_lt_two {q s : ℝ} {u : Vec n}
    (hq : q ≤ 1) (hqs : 0 ≤ q * s) (hu : ∀ i, 0 ≤ u i)
    (hcube : s • u ∈ cube n) (hus : scoreSum u = 1) (j : Fin n) :
    columnIntegral q s u j ≤ Real.exp (q * s * u j) := by
  unfold columnIntegral
  calc
    _ ≤ ∫ z in (0 : ℝ)..(q * s), Real.exp (q * s * u j) * Real.exp (-z) :=
      intervalIntegral.integral_mono_on hqs ((continuous_columnIntegrand u j).intervalIntegrable 0 (q * s))
        ((show Continuous (fun z : ℝ ↦ Real.exp (q * s * u j) * Real.exp (-z)) by fun_prop).intervalIntegrable 0 (q * s))
        (fun z hz ↦ by
          calc
            _ ≤ Real.exp (-(1 - u j) * z) :=
              columnIntegrand_le_exp hq hz hu hcube hus j
            _ ≤ _ := by
              rw [← Real.exp_add]
              exact Real.exp_le_exp.mpr (by
                nlinarith [mul_le_mul_of_nonneg_right hz.2 (hu j)]))
    _ = Real.exp (q * s * u j) * (1 - Real.exp (-(q * s))) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simp [intervalIntegral.integral_comp_neg, integral_exp]
    _ ≤ Real.exp (q * s * u j) := mul_le_of_le_one_right (Real.exp_nonneg _)
      (sub_le_self _ (Real.exp_nonneg _))

/-- The radial weight is nonnegative and bounded by both an absolute constant
and the $n$th power of the integration length. -/
theorem radialWeight_bounds {q s : ℝ} {u : Vec n}
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hu : ∀ i, 0 ≤ u i) (hus : scoreSum u = 1) :
    radialWeight n q s u ∈ Icc 0 (min (Real.exp 2) ((q * s) ^ n)) := by
  classical
  have hqs : 0 ≤ q * s := mul_nonneg hq.1.le hs.le
  unfold radialWeight
  split_ifs with hcube
  · have hnn := columnIntegral_nonneg hq.2 hqs hu hcube
    refine ⟨Finset.prod_nonneg (fun j _ ↦ hnn j), le_min ?_ ?_⟩
    · by_cases hlarge : 2 ≤ s
      · calc
          _ ≤ ∏ j, Real.exp (2 * u j) :=
            Finset.prod_le_prod₀ (fun j _ ↦ hnn j)
              (fun j _ ↦ columnIntegral_le_exp_of_two_le hq.2 hqs hlarge hu hcube hus j)
          _ = Real.exp 2 := by
            rw [← Real.exp_sum, ← Finset.mul_sum]
            change Real.exp (2 * scoreSum u) = _
            rw [hus, mul_one]
      · calc
          _ ≤ ∏ j, Real.exp (q * s * u j) :=
            Finset.prod_le_prod₀ (fun j _ ↦ hnn j)
              (fun j _ ↦ columnIntegral_le_exp_of_lt_two hq.2 hqs hu hcube hus j)
          _ = Real.exp (q * s) := by
            rw [← Real.exp_sum, ← Finset.mul_sum]
            change Real.exp (q * s * scoreSum u) = _
            rw [hus, mul_one]
          _ ≤ Real.exp 2 :=
            Real.exp_le_exp.mpr ((mul_le_of_le_one_left hs.le hq.2).trans (le_of_not_ge hlarge))
    · calc
        _ ≤ ∏ _j : Fin n, (q * s) :=
          Finset.prod_le_prod₀ (fun j _ ↦ hnn j)
            (fun j _ ↦ columnIntegral_le_length hq.2 hqs hu hcube j)
        _ = _ := by simp
  · exact ⟨le_rfl, le_min (Real.exp_nonneg _) (pow_nonneg hqs _)⟩

/-- The radial density satisfies the same uniform bounds as the radial weight
when the averaging law is supported on the simplex. -/
theorem radialDensity_bounds {q s : ℝ} [IsProbabilityMeasure (simplexLaw n)]
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s)
    (hSimplex : ∀ᵐ u ∂simplexLaw n, (∀ i, 0 ≤ u i) ∧ scoreSum u = 1) :
    radialDensity n q s ∈ Icc 0 (min (Real.exp 2) ((q * s) ^ n)) := by
  have hb : ∀ᵐ u ∂simplexLaw n,
      radialWeight n q s u ∈ Icc 0 (min (Real.exp 2) ((q * s) ^ n)) := by
    filter_upwards [hSimplex] with u hu
    exact radialWeight_bounds hq hs hu.1 hu.2
  have hnonneg : 0 ≤ᵐ[simplexLaw n] radialWeight n q s := by
    filter_upwards [hb] with _ hu using hu.1
  have hupper : ∀ᵐ u ∂simplexLaw n, radialWeight n q s u ≤ min (Real.exp 2) ((q * s) ^ n) := by
    filter_upwards [hb] with _ hu using hu.2
  refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
  unfold radialDensity
  have hle := integral_mono_of_nonneg hnonneg
    (integrable_const (min (Real.exp 2) ((q * s) ^ n))) hupper
  simpa using hle

/-- A bound on the radial weight away from a small exceptional set yields the
corresponding bound on its simplex average. -/
theorem abs_radialDensity_sub_exp_neg_one_le {q s η : ℝ} {good : Set (Vec n)}
    [IsProbabilityMeasure (simplexLaw n)]
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) (hη : 0 ≤ η)
    (hSimplex : ∀ᵐ u ∂simplexLaw n, (∀ i, 0 ≤ u i) ∧ scoreSum u = 1)
    (hGood : MeasurableSet good)
    (hClose : ∀ u ∈ good, |radialWeight n q s u - Real.exp (-1)| ≤ η) :
    |radialDensity n q s - Real.exp (-1)| ≤
      η + (Real.exp 2 + Real.exp (-1)) * (simplexLaw n).real goodᶜ := by
  let f : Vec n → ℝ := radialWeight n q s
  let C := Real.exp 2 + Real.exp (-1)
  have hb : ∀ᵐ u ∂simplexLaw n, f u ∈ Icc 0 (Real.exp 2) := by
    filter_upwards [hSimplex] with u hu
    have h := radialWeight_bounds hq hs hu.1 hu.2
    exact ⟨h.1, h.2.trans (min_le_left _ _)⟩
  have hf : Integrable f (simplexLaw n) := by
    refine Integrable.of_bound ?_ (Real.exp 2) ?_
    · exact ((measurable_radialWeight n q).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [hb] with u hu
      simpa [Real.norm_eq_abs, abs_of_nonneg hu.1] using hu.2
  have hg : Integrable (goodᶜ.indicator (fun _ : Vec n ↦ C)) (simplexLaw n) :=
    (integrable_const C).indicator hGood.compl
  have hbound : ∀ᵐ u ∂simplexLaw n,
      |f u - Real.exp (-1)| ≤ η + goodᶜ.indicator (fun _ : Vec n ↦ C) u := by
    filter_upwards [hb] with u hu
    by_cases hm : u ∈ good
    · simpa [hm, f] using hClose u hm
    · have h : |f u - Real.exp (-1)| ≤ C := by
        calc
          _ ≤ |f u| + |Real.exp (-1)| := abs_sub _ _
          _ = f u + Real.exp (-1) := by
            rw [abs_of_nonneg hu.1, abs_of_nonneg (Real.exp_nonneg _)]
          _ ≤ C := by
            dsimp [C]
            linarith [hu.2]
      simpa [hm, add_comm] using h.trans (le_add_of_nonneg_right hη)
  calc
    _ = |∫ u, f u - Real.exp (-1) ∂simplexLaw n| := by
      rw [integral_sub hf (integrable_const _)]
      simp [f, radialDensity]
    _ ≤ ∫ u, |f u - Real.exp (-1)| ∂simplexLaw n := abs_integral_le_integral_abs
    _ ≤ ∫ u, η + goodᶜ.indicator (fun _ : Vec n ↦ C) u ∂simplexLaw n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
        ((integrable_const η).add hg) hbound
    _ = _ := by
      rw [integral_add (integrable_const η) hg, integral_indicator_const _ hGood.compl]
      simp [C, mul_comm]

end SupercriticalLogRank
