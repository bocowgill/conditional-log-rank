module

public import SupercriticalLogRank.MarketBasics

@[expose] public section

/-! Concentration of a uniform simplex vector obtained by normalizing independent exponentials. -/

open Filter MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal Topology BigOperators
namespace SupercriticalLogRank

noncomputable section

private instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure zero_lt_one

private theorem expMeasure_one_density :
    expMeasure 1 = volume.withDensity (exponentialPDF 1) := rfl

private theorem expMeasure_one_pdf_measurable : Measurable (exponentialPDF 1) :=
  (measurable_exponentialPDFReal 1).ennreal_ofReal

private theorem expMeasure_one_pdf_lt_top : ∀ᵐ x ∂volume, exponentialPDF 1 x < ⊤ := by
  exact ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top

private theorem expMeasure_one_pdf_smul_pow (k : ℕ) :
    (fun x : ℝ ↦ (exponentialPDF 1 x).toReal • x ^ k) =
      (Ici (0 : ℝ)).indicator (fun x ↦ Real.exp (-x) * x ^ k) := by
  funext x
  by_cases hx : 0 ≤ x
  · simp [exponentialPDF_eq, hx, Real.exp_nonneg]
  · simp [exponentialPDF_eq, hx]

theorem integrable_pow_expMeasure_one (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (expMeasure 1) := by
  rw [expMeasure_one_density,
    integrable_withDensity_iff_integrable_smul' expMeasure_one_pdf_measurable
      expMeasure_one_pdf_lt_top,
    expMeasure_one_pdf_smul_pow, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using Real.GammaIntegral_convergent h

theorem integral_pow_expMeasure_one (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂expMeasure 1) = (k.factorial : ℝ) := by
  rw [expMeasure_one_density,
    integral_withDensity_eq_integral_toReal_smul expMeasure_one_pdf_measurable
      expMeasure_one_pdf_lt_top,
    expMeasure_one_pdf_smul_pow, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  have h : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simpa only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using
    (Real.Gamma_eq_integral h).symm

theorem expMeasure_one_real_Ioi {x : ℝ} (hx : 0 ≤ x) :
    (expMeasure 1).real (Ioi x) = Real.exp (-x) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq zero_lt_one, probReal_univ, ite_eq_left hx, one_mul, sub_sub_cancel]

theorem ae_pos_expMeasure_one : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  rw [ae_iff]
  simp only [not_lt]
  change expMeasure 1 (Iic 0) = 0
  rw [← measureReal_eq_zero_iff, ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one]
  simp


open Filter
open scoped Topology

private theorem expVectorMeasure_real_coord_gt (n : ℕ) (i : Fin n) {x : ℝ} (hx : 0 ≤ x) :
    (expVectorMeasure n).real {v | x < v i} = Real.exp (-x) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hpres : MeasurePreserving (Function.eval i) (expVectorMeasure n) (expMeasure 1) :=
    measurePreserving_eval (μ := fun _ : Fin n ↦ expMeasure 1) i
  change (expVectorMeasure n).real (Function.eval i ⁻¹' Ioi x) = _
  rw [measureReal_def, ← Measure.map_apply hpres.measurable measurableSet_Ioi, hpres.map_eq,
    ← measureReal_def, expMeasure_one_real_Ioi hx]

theorem expVectorMeasure_real_exists_gt_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (expVectorMeasure n).real {v | ∃ i, x < v i} ≤ (n : ℝ) * Real.exp (-x) := by
  have h : {v : Vec n | ∃ i, x < v i} = ⋃ i : Fin n, {v | x < v i} := by ext; simp
  rw [h]
  apply (measureReal_iUnion_fintype_le _).trans
  simp [expVectorMeasure_real_coord_gt n _ hx]

theorem tendsto_expVectorMeasure_real_exists_gt_two_log :
    Tendsto (fun n : ℕ ↦ (expVectorMeasure n).real {v | ∃ i, 2 * Real.log n < v i})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ)))
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  · exact .of_forall fun _ ↦ measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hp : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    refine (expVectorMeasure_real_exists_gt_le n (x := 2 * Real.log n) (by positivity)).trans_eq ?_
    rw [show -(2 * Real.log n) = -(Real.log n + Real.log n) by ring, Real.exp_neg, Real.exp_add,
      Real.exp_log hp]
    field_simp

private def sampleMean {n : ℕ} (g : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g (x i)

private theorem measurable_sampleMean {n : ℕ} {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (sampleMean (n := n) g) := by
  unfold sampleMean
  fun_prop (disch := apply hg)

private theorem sampleMean_tail_le {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ}
    (hg : MemLp g 2 (expMeasure 1)) {c : ℝ} (hc : 0 < c) :
    expVectorMeasure n {x | c ≤ |sampleMean g x - ∫ a, g a ∂expMeasure 1|}
      ≤ ENNReal.ofReal (variance g (expMeasure 1) / (n * c ^ 2)) := by
  have hnc : (0 : ℝ) < n := by exact_mod_cast hn
  let f : Fin n → (Fin n → ℝ) → ℝ := fun i x ↦ g (x i)
  have hmem (i : Fin n) : MemLp (f i) 2 (expVectorMeasure n) :=
    hg.comp_measurePreserving (measurePreserving_eval _ i)
  have hs : MemLp (∑ i : Fin n, f i) 2 (expVectorMeasure n) :=
    memLp_finsetSum' _ fun i _ ↦ hmem i
  have hs' : MemLp (sampleMean (n := n) g) 2 (expVectorMeasure n) := by
    convert hs.const_mul ((n : ℝ)⁻¹) using 1
    ext x
    simp [sampleMean, f, Finset.sum_apply]
  have hIg (i : Fin n) : (∫ x, f i x ∂expVectorMeasure n) = ∫ a, g a ∂expMeasure 1 := by
    have hm : MeasurePreserving (Function.eval i) (expVectorMeasure n) (expMeasure 1) :=
      measurePreserving_eval _ i
    change (∫ x, g ((Function.eval i) x) ∂expVectorMeasure n) = _
    rw [← integral_map hm.measurable.aemeasurable, hm.map_eq]
    rw [hm.map_eq]
    exact hg.aestronglyMeasurable
  have hi : (∫ x, sampleMean g x ∂expVectorMeasure n) = ∫ a, g a ∂expMeasure 1 := by
    unfold sampleMean
    rw [integral_const_mul, integral_finsetSum]
    · rw [Finset.sum_congr rfl fun i _ ↦ hIg i]
      simp [hnc.ne']
    · exact fun i _ ↦ (hmem i).integrable (by norm_num)
  have hvs : variance (fun x : Fin n → ℝ ↦ ∑ i, g (x i)) (expVectorMeasure n) =
      n * variance g (expMeasure 1) := by
    have hv := variance_sum_pi (ι := Fin n) (μ := fun _ ↦ expMeasure 1)
      (X := fun _ ↦ g) (fun _ ↦ hg)
    rw [show (fun x : Fin n → ℝ ↦ ∑ i, g (x i)) = ∑ i : Fin n, f i by
      ext x
      simp [f, Finset.sum_apply]]
    simpa [f, expVectorMeasure] using hv
  have hv : variance (sampleMean (n := n) g) (expVectorMeasure n) =
      variance g (expMeasure 1) / n := by
    unfold sampleMean
    rw [variance_const_mul, hvs]
    field_simp
  have ht := meas_ge_le_variance_div_sq hs' hc
  rw [hi, hv] at ht
  simpa [div_div] using ht


private theorem tendsto_sampleMean_tail {g : ℝ → ℝ}
    (hg : MemLp g 2 (expMeasure 1)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (expVectorMeasure n).real
      {x | c ≤ |sampleMean g x - ∫ a, g a ∂expMeasure 1|}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ variance g (expMeasure 1) / ((n : ℝ) * c ^ 2))
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    convert h.const_mul (variance g (expMeasure 1) / c ^ 2) using 1
    · ext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (sampleMean_tail_le hn hg hc)
  simpa [measureReal_def, ENNReal.toReal_ofReal
    (div_nonneg (variance_nonneg _ _) (by positivity : (0 : ℝ) ≤ (n : ℝ) * c ^ 2))] using h

private theorem memLp_pow_expMeasure_one (k : ℕ) :
    MemLp (fun x : ℝ ↦ x ^ k) 2 (expMeasure 1) := by
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  simpa only [pow_mul] using integrable_pow_expMeasure_one (k * 2)

private theorem tendsto_firstMoment_tail {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (expVectorMeasure n).real
      {x | c ≤ |sampleMean (fun a ↦ a) x - 1|}) atTop (𝓝 0) := by
  have h := tendsto_sampleMean_tail (memLp_pow_expMeasure_one 1) hc
  rw [integral_pow_expMeasure_one] at h
  simpa using h

private theorem tendsto_secondMoment_tail {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (expVectorMeasure n).real
      {x | c ≤ |sampleMean (fun a ↦ a ^ 2) x - 2|}) atTop (𝓝 0) := by
  have h := tendsto_sampleMean_tail (memLp_pow_expMeasure_one 2) hc
  rw [integral_pow_expMeasure_one] at h
  norm_num [Nat.factorial] at h
  exact h

theorem ae_pos_expVectorMeasure (n : ℕ) :
    ∀ᵐ x ∂expVectorMeasure n, ∀ i, 0 < x i := by
  rw [ae_all_iff]
  intro i
  have h : MeasurePreserving (Function.eval i) (expVectorMeasure n) (expMeasure 1) :=
    measurePreserving_eval _ i
  exact h.quasiMeasurePreserving.ae ae_pos_expMeasure_one

theorem ae_simplexLaw (n : ℕ) (hn : 0 < n) :
    ∀ᵐ u ∂simplexLaw n, (∀ i, 0 < u i) ∧ scoreSum u = 1 := by
  unfold simplexLaw
  rw [ae_map_iff (measurable_simplexNormalize n).aemeasurable]
  · filter_upwards [ae_pos_expVectorMeasure n] with e he
    have hs : 0 < scoreSum e := by
      unfold scoreSum
      exact Finset.sum_pos (fun i _ ↦ he i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact ⟨fun i ↦ div_pos (he i) hs, by
      rw [scoreSum, ← Finset.sum_div]
      exact div_self hs.ne'⟩
  · convert (MeasurableSet.iInter fun i : Fin n ↦ measurableSet_lt (measurable_const (a := (0 : ℝ)))
        (measurable_pi_apply i)).inter
      (measurableSet_eq_fun (measurable_scoreSum n) (measurable_const (a := (1 : ℝ)))) using 1
    ext u
    simp

theorem tendsto_simplexLaw_max_tail :
    Tendsto (fun n : ℕ ↦ (simplexLaw n).real
      {u | ∃ i, 4 * Real.log n / (n : ℝ) < u i}) atTop (𝓝 0) := by
  have hlim := (tendsto_firstMoment_tail (c := 1 / 2) (by norm_num)).add
    tendsto_expVectorMeasure_real_exists_gt_two_log
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  let A : Set (Vec n) := {x | 1 / 2 ≤ |sampleMean (fun a ↦ a) x - 1|}
  let B : Set (Vec n) := {x | ∃ i, 2 * Real.log n < x i}
  let S : Set (Vec n) := {u | ∃ i, 4 * Real.log n / (n : ℝ) < u i}
  have hS : MeasurableSet S := by
    change MeasurableSet {u : Vec n | ∃ i, 4 * Real.log n / (n : ℝ) < u i}
    rw [show {u : Vec n | ∃ i, 4 * Real.log n / (n : ℝ) < u i} =
        ⋃ i : Fin n, {u : Vec n | 4 * Real.log n / (n : ℝ) < u i} by ext; simp]
    exact MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i)
  change (simplexLaw n).real S ≤ (expVectorMeasure n).real A + (expVectorMeasure n).real B
  rw [simplexLaw, map_measureReal_apply (measurable_simplexNormalize n) hS]
  refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
  intro e he
  by_contra h
  have ha : e ∉ A := fun hA ↦ h (Or.inl hA)
  have hb : e ∉ B := fun hB ↦ h (Or.inr hB)
  change ¬ (1 / 2 : ℝ) ≤ |sampleMean (fun a ↦ a) e - 1| at ha
  have hmean : (1 / 2 : ℝ) < sampleMean (fun a ↦ a) e := by
    have he' := (abs_lt.mp (lt_of_not_ge ha)).1
    linarith
  have hs : (n : ℝ) / 2 < scoreSum e := by
    unfold sampleMean at hmean
    rw [inv_mul_eq_div] at hmean
    exact (lt_div_iff₀ hn').mp hmean |>.trans_eq' (by ring)
  have hs' : 0 < scoreSum e := lt_trans (by positivity) hs
  obtain ⟨i, hi⟩ := he
  change 4 * Real.log n / (n : ℝ) < e i / scoreSum e at hi
  have hlow := (lt_div_iff₀ hs').mp hi
  have hupper : e i ≤ 2 * Real.log n := le_of_not_gt fun h' ↦ hb ⟨i, h'⟩
  have hmiddle : 2 * Real.log n ≤ 4 * Real.log n / (n : ℝ) * scoreSum e := calc
    2 * Real.log n = 4 * Real.log n / (n : ℝ) * ((n : ℝ) / 2) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs.le (by positivity)
  exact (not_lt_of_ge (hupper.trans hmiddle)) hlow

private theorem normalized_square_sum {n : ℕ} (hn : 0 < n) (e : Vec n)
    (hs : scoreSum e ≠ 0) :
    (n : ℝ) * ∑ i, (e i / scoreSum e) ^ 2 =
      sampleMean (fun a ↦ a ^ 2) e / (sampleMean (fun a ↦ a) e) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sampleMean
  simp only [div_pow, ← Finset.sum_div]
  change (n : ℝ) * ((∑ i, e i ^ 2) / scoreSum e ^ 2) =
    ((n : ℝ)⁻¹ * ∑ i, e i ^ 2) / ((n : ℝ)⁻¹ * scoreSum e) ^ 2
  field_simp

theorem tendsto_simplexLaw_sq_tail {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (simplexLaw n).real
      {u | η ≤ |(n : ℝ) * (∑ i, (u i) ^ 2) - 2|}) atTop (𝓝 0) := by
  let F : ℝ × ℝ → ℝ := fun x ↦ x.2 / x.1 ^ 2
  have hF : ContinuousAt F ((1 : ℝ), (2 : ℝ)) :=
    continuous_snd.continuousAt.div (continuous_fst.continuousAt.pow 2) (by norm_num)
  obtain ⟨d, hd, hcont⟩ := (Metric.continuousAt_iff.mp hF) η hη
  let c := min d (1 / 2)
  have hc : 0 < c := lt_min hd (by norm_num)
  have hlim := (tendsto_firstMoment_tail hc).add (tendsto_secondMoment_tail hc)
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let A : Set (Vec n) := {e | c ≤ |sampleMean (fun a ↦ a) e - 1|}
  let B : Set (Vec n) := {e | c ≤ |sampleMean (fun a ↦ a ^ 2) e - 2|}
  let S : Set (Vec n) := {u | η ≤ |(n : ℝ) * (∑ i, (u i) ^ 2) - 2|}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (by fun_prop (disch := exact measurable_pi_apply _))
  change (simplexLaw n).real S ≤ (expVectorMeasure n).real A + (expVectorMeasure n).real B
  rw [simplexLaw, map_measureReal_apply (measurable_simplexNormalize n) hS]
  refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
  intro e he
  by_contra h
  have ha : |sampleMean (fun a ↦ a) e - 1| < c := lt_of_not_ge fun hA ↦ h (Or.inl hA)
  have hb : |sampleMean (fun a ↦ a ^ 2) e - 2| < c :=
    lt_of_not_ge fun hB ↦ h (Or.inr hB)
  have hs : scoreSum e ≠ 0 := by
    intro hs
    have hh : sampleMean (fun a ↦ a) e = 0 := by
      rw [sampleMean]
      change (n : ℝ)⁻¹ * scoreSum e = _
      simp [hs]
    rw [hh, zero_sub, abs_neg, abs_one] at ha
    linarith [le_min_iff.mp (le_refl c) |>.2]
  have hd' : dist (sampleMean (fun a ↦ a) e, sampleMean (fun a ↦ a ^ 2) e) (1, 2) < d := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨ha.trans_le (min_le_left _ _), hb.trans_le (min_le_left _ _)⟩
  have hlt := hcont hd'
  change η ≤ |(n : ℝ) * (∑ i, (e i / scoreSum e) ^ 2) - 2| at he
  rw [normalized_square_sum hn e hs] at he
  have hF12 : F (1, 2) = 2 := by norm_num [F]
  rw [Real.dist_eq, hF12] at hlt
  exact (not_lt_of_ge he) hlt

/-- Simplex points with coordinate and quadratic bounds used in the column expansion. -/
def simplexTypical (n : ℕ) (η : ℝ) : Set (Vec n) :=
  {u | ((∀ i, 0 < u i) ∧ scoreSum u = 1) ∧
    (∀ i, u i ≤ 4 * Real.log n / (n : ℝ)) ∧
    |(n : ℝ) * (∑ i, (u i) ^ 2) - 2| < η}

theorem measurableSet_simplexTypical (n : ℕ) (η : ℝ) :
    MeasurableSet (simplexTypical n η) := by
  have hpos : MeasurableSet {u : Vec n | ∀ i, 0 < u i} := by
    rw [show {u : Vec n | ∀ i, 0 < u i} =
      ⋂ i : Fin n, {u : Vec n | 0 < u i} by ext; simp]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i)
  have hmax : MeasurableSet {u : Vec n | ∀ i, u i ≤ 4 * Real.log n / (n : ℝ)} := by
    rw [show {u : Vec n | ∀ i, u i ≤ 4 * Real.log n / (n : ℝ)} =
      ⋂ i : Fin n, {u : Vec n | u i ≤ 4 * Real.log n / (n : ℝ)} by ext; simp]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_pi_apply i) measurable_const
  have hQ : Measurable (fun u : Vec n ↦ |(n : ℝ) * (∑ i, (u i) ^ 2) - 2|) := by
    fun_prop (disch := exact measurable_pi_apply _)
  exact (hpos.inter (measurableSet_eq_fun (measurable_scoreSum n) measurable_const)).inter
    (hmax.inter (measurableSet_lt hQ measurable_const))

theorem tendsto_simplexLaw_typical_compl {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (simplexLaw n).real (simplexTypical n η)ᶜ) atTop (𝓝 0) := by
  have hlim := tendsto_simplexLaw_max_tail.add (tendsto_simplexLaw_sq_tail hη)
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let A : Set (Vec n) := {u | ∃ i, 4 * Real.log n / (n : ℝ) < u i}
  let B : Set (Vec n) := {u | η ≤ |(n : ℝ) * (∑ i, (u i) ^ 2) - 2|}
  let C : Set (Vec n) := {u | ¬ ((∀ i, 0 < u i) ∧ scoreSum u = 1)}
  have hC : (simplexLaw n).real C = 0 := by
    rw [measureReal_eq_zero_iff]
    have h := ae_simplexLaw n hn
    rwa [ae_iff] at h
  have hsub : (simplexTypical n η)ᶜ ⊆ C ∪ (A ∪ B) := by
    intro u hu
    by_contra h
    have hc : (∀ i, 0 < u i) ∧ scoreSum u = 1 := by
      by_contra hc
      exact h (Or.inl hc)
    have ha (i : Fin n) : u i ≤ 4 * Real.log n / (n : ℝ) :=
      le_of_not_gt fun hi ↦ h (Or.inr (Or.inl ⟨i, hi⟩))
    have hb : |(n : ℝ) * (∑ i, (u i) ^ 2) - 2| < η :=
      lt_of_not_ge fun hb ↦ h (Or.inr (Or.inr hb))
    exact hu ⟨hc, ha, hb⟩
  change (simplexLaw n).real (simplexTypical n η)ᶜ ≤
    (simplexLaw n).real A + (simplexLaw n).real B
  calc
    _ ≤ (simplexLaw n).real (C ∪ (A ∪ B)) := measureReal_mono hsub
    _ ≤ (simplexLaw n).real C + (simplexLaw n).real (A ∪ B) := measureReal_union_le _ _
    _ ≤ _ := by simpa [hC] using
      (measureReal_union_le (μ := simplexLaw n) A B)

end
end SupercriticalLogRank
