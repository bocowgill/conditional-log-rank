module

public import SupercriticalLogRank.MarketBasics

@[expose] public section

/-! Radial integration in a finite real coordinate space. -/

namespace SupercriticalLogRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

/-- Complete the simplex coordinates by choosing coordinate zero so the sum is one. -/
def completeSimplex {n : ℕ} (v : Vec n) : Vec (n + 1) :=
  Fin.cons (1 - scoreSum v) v

@[simp]
theorem scoreSum_completeSimplex {n : ℕ} (v : Vec n) :
    scoreSum (completeSimplex v) = 1 := by
  simp [completeSimplex, scoreSum, Fin.sum_univ_succ]

@[simp]
theorem scoreSum_smul {n : ℕ} (s : ℝ) (v : Vec n) :
    scoreSum (s • v) = s * scoreSum v := by
  simp [scoreSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

@[fun_prop]
theorem measurable_completeSimplex {n : ℕ} :
    Measurable (completeSimplex : Vec n → Vec (n + 1)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [completeSimplex, Fin.cons_zero, scoreSum]
    fun_prop
  · simp only [completeSimplex, Fin.cons_succ]
    fun_prop

private theorem lintegral_dilate {n : ℕ} {s : ℝ} (hs : 0 < s)
    {g : Vec n → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z) = ENNReal.ofReal (s ^ n) * ∫⁻ v, g (s • v) := by
  calc
    (∫⁻ z, g z) = ∫⁻ z : Vec n, g (s • (s⁻¹ • z)) := by
      simp [smul_smul, mul_inv_cancel₀ hs.ne']
    _ = ∫⁻ v, g (s • v) ∂Measure.map (s⁻¹ • ·) volume :=
      (lintegral_map (hg.comp (measurable_const_smul s))
        (measurable_const_smul s⁻¹)).symm
    _ = ENNReal.ofReal (s ^ n) * ∫⁻ v, g (s • v) := by
      rw [Measure.map_addHaar_smul volume (inv_ne_zero hs.ne'), lintegral_smul_measure]
      simp [Module.finrank_fintype_fun_eq_card, inv_pow, abs_of_pos (pow_pos hs n)]

private theorem measurable_cons {n : ℕ} :
    Measurable (fun p : ℝ × Vec n ↦ (Fin.cons p.1 p.2 : Vec (n + 1))) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : ℝ × Vec n → ℝ))
  · simp only [Fin.cons_succ]
    fun_prop

/-- Radial integration, first translating the leading coordinate by the sum of the remaining
coordinates and then dilating the remaining coordinates by the resulting radius. -/
theorem lintegral_sum_pos_eq_radial {n : ℕ} {f : Vec (n + 1) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x in {x : Vec (n + 1) | 0 < scoreSum x}, f x) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ n) *
        (∫⁻ v : Vec n, f (s • completeSimplex v)) := by
  classical
  let C : ℝ × Vec n → Vec (n + 1) := fun p ↦ Fin.cons p.1 p.2
  let D : ℝ × Vec n → Vec (n + 1) := fun p ↦ Fin.cons (p.1 - scoreSum p.2) p.2
  let g : ℝ × Vec n → ℝ≥0∞ := fun p ↦ if 0 < p.1 then f (D p) else 0
  have hC : Measurable C := measurable_cons
  have hD : Measurable D := hC.comp <|
    (measurable_fst.sub ((measurable_scoreSum n).comp measurable_snd)).prodMk measurable_snd
  have hg : Measurable g := by
    exact (hf.comp hD).ite (measurableSet_lt measurable_const measurable_fst) measurable_const
  have hpositive : MeasurableSet {x : Vec (n + 1) | 0 < scoreSum x} :=
    measurableSet_lt measurable_const (measurable_scoreSum _)
  have he : ∀ p : ℝ × Vec n,
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm p = C p := by
    intro p
    simp [C, Fin.insertNthEquiv]
  have hchange :
      (∫⁻ x, ({x : Vec (n + 1) | 0 < scoreSum x} : Set _).indicator f x) =
      ∫⁻ p : ℝ × Vec n, ({x : Vec (n + 1) | 0 < scoreSum x} : Set _).indicator f (C p)
        ∂((volume : Measure ℝ).prod volume) := by
    symm
    simpa only [he, Measure.volume_eq_prod] using
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm).lintegral_comp
        (hf.indicator hpositive)
  rw [← lintegral_indicator hpositive, hchange]
  calc
    _ = ∫⁻ v : Vec n, ∫⁻ t : ℝ, g (t + scoreSum v, v) := by
      have hm : Measurable (fun p : ℝ × Vec n ↦
          ({x : Vec (n + 1) | 0 < scoreSum x} : Set _).indicator f (C p)) :=
        (hf.indicator hpositive).comp hC
      rw [lintegral_prod_symm' _ hm]
      congr 1
      funext v
      congr 1
      funext t
      simp [g, D, C, Set.indicator, scoreSum, Fin.sum_univ_succ]
    _ = ∫⁻ v : Vec n, ∫⁻ s : ℝ, g (s, v) := by
      congr 1
      funext v
      exact lintegral_add_right_eq_self (fun s : ℝ ↦ g (s, v)) (scoreSum v)
    _ = ∫⁻ s : ℝ, ∫⁻ v : Vec n, g (s, v) :=
      (lintegral_lintegral_swap (f := fun s v ↦ g (s, v)) hg.aemeasurable).symm
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v : Vec n, f (D (s, v)) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      congr 1
      funext s
      by_cases hs : 0 < s <;> simp [g, Set.indicator, hs]
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ n) *
        (∫⁻ v : Vec n, f (s • completeSimplex v)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hms : Measurable (fun v : Vec n ↦ f (D (s, v))) :=
        hf.comp (hD.comp (measurable_const.prodMk measurable_id))
      change (∫⁻ v : Vec n, f (D (s, v))) = _
      rw [lintegral_dilate hs hms]
      congr 1
      congr 1
      funext v
      congr 1
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [D, completeSimplex, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [D, completeSimplex, Pi.smul_apply]

/-- The positive orthant in the coordinate space. -/
def positiveOrthant (n : ℕ) : Set (Vec n) := {x | ∀ i, 0 < x i}

/-- Coordinates on the interior of the simplex, with coordinate zero omitted. -/
def simplexTail (n : ℕ) : Set (Vec n) := completeSimplex ⁻¹' positiveOrthant (n + 1)

theorem measurableSet_positiveOrthant (n : ℕ) : MeasurableSet (positiveOrthant n) := by
  have h : positiveOrthant n = Set.univ.pi (fun _ : Fin n ↦ Ioi (0 : ℝ)) := by
    ext x
    simp [positiveOrthant]
  rw [h]
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioi

theorem measurableSet_simplexTail (n : ℕ) : MeasurableSet (simplexTail n) :=
  measurable_completeSimplex (measurableSet_positiveOrthant (n + 1))

private theorem sum_pos_of_mem_positiveOrthant {n : ℕ} {x : Vec (n + 1)}
    (hx : x ∈ positiveOrthant (n + 1)) : 0 < scoreSum x := by
  unfold scoreSum
  exact Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty

private theorem smul_mem_positiveOrthant {n : ℕ} {s : ℝ} (hs : 0 < s) (x : Vec n) :
    s • x ∈ positiveOrthant n ↔ x ∈ positiveOrthant n := by
  change (∀ i, 0 < s * x i) ↔ ∀ i, 0 < x i
  simp only [mul_pos_iff_of_pos_left hs]

private theorem normalize_completeSimplex {n : ℕ} {s : ℝ} (hs : 0 < s) (v : Vec n) :
    (fun i ↦ (s • completeSimplex v) i / scoreSum (s • completeSimplex v)) =
      completeSimplex v := by
  ext i
  simp [Pi.smul_apply, smul_eq_mul, hs.ne']

/-- Tonelli for a product of one-coordinate test functions. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmeas : Measurable (fun x : Fin (n + 1) → ℝ ↦ ∏ i, f i (x i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (hf i).comp (measurable_pi_apply i))
    have he := (measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))).symm.lintegral_comp hmeas
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_succ, Fin.cons_zero,
      Fin.zero_succAbove, cast_eq] at he
    have htail : Measurable (fun x : Fin n → ℝ ↦ ∏ i, f i.succ (x i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (hf i.succ).comp (measurable_pi_apply i))
    conv_lhs => simp only [Fin.prod_univ_succ]
    rw [← he, lintegral_prod_mul (hf 0).aemeasurable htail.aemeasurable,
      ih (fun i ↦ μ i.succ) (fun i ↦ f i.succ) (fun i ↦ hf i.succ), Fin.prod_univ_succ]


/-- The density of independent exponential coordinates is the product density. -/
theorem exp_pi_density (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ expMeasure 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x ↦ ∏ i, exponentialPDF 1 (x i)) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  refine Measure.pi_eq (fun s hs ↦ ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  rw [lintegral_fin_prod_eq_prod _ (fun _ ↦ exponentialPDF 1)
    (fun _ ↦ (measurable_exponentialPDFReal _).ennreal_ofReal)]
  simp_rw [expMeasure, gammaMeasure, withDensity_apply _ (hs _)]
  rfl

/-- The product density on the nonnegative orthant. -/
theorem exp_pi_density_formula {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, exponentialPDF 1 (x i)) =
      ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} : Set _).indicator
        (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i)))) x := by
  classical
  by_cases hx : ∀ i, 0 ≤ x i
  · rw [indicator_of_mem (show x ∈ {x : Fin n → ℝ | ∀ i, 0 ≤ x i} from hx)]
    simp_rw [exponentialPDF_of_nonneg (hx _), one_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
      ← Real.exp_sum, Finset.sum_neg_distrib]
  · rw [indicator_of_notMem (show x ∉ {x : Fin n → ℝ | ∀ i, 0 ≤ x i} from hx)]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (exponentialPDF_of_neg hi)

/-- Removing the coordinate hyperplanes gives the same exponential law. -/
theorem exp_pi_density_pos (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ expMeasure 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (({x : Fin n → ℝ | ∀ i, 0 < x i} : Set _).indicator
          (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i))))) := by
  rw [exp_pi_density]
  apply withDensity_congr_ae
  have hne : ∀ᵐ x : Fin n → ℝ ∂volume, ∀ i, x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact Measure.ae_eval_ne (fun _ ↦ volume) i 0
  filter_upwards [hne] with x hx
  rw [exp_pi_density_formula]
  have hiff : (∀ i, 0 ≤ x i) ↔ ∀ i, 0 < x i :=
    ⟨fun h i ↦ lt_of_le_of_ne (h i) (Ne.symm (hx i)), fun h i ↦ (h i).le⟩
  simp [Set.indicator, hiff]

private theorem lintegral_gamma_nat (n : ℕ) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ n) * ENNReal.ofReal (Real.exp (-s))) =
      (n.factorial : ℝ≥0∞) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hi : IntegrableOn (fun s : ℝ ↦ Real.exp (-s) * s ^ n) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      (Real.GammaIntegral_convergent hp)
  have hne : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s : ℝ ↦ Real.exp (-s) * s ^ n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hs.le _)
  have heq : (∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ n) = (n.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial n, Real.Gamma_eq_integral hp]
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s) * s ^ n) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s _
      change ENNReal.ofReal (s ^ n) * ENNReal.ofReal (Real.exp (-s)) =
        ENNReal.ofReal (Real.exp (-s) * s ^ n)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi hne, heq, ENNReal.ofReal_natCast]

/-- The uniform simplex law written in the coordinates with coordinate zero omitted. -/
theorem lintegral_simplexLaw_eq {n : ℕ} {g : Vec (n + 1) → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ u, g u ∂simplexLaw (n + 1)) =
      (n.factorial : ℝ≥0∞) * ∫⁻ v in simplexTail n, g (completeSimplex v) := by
  classical
  let d : Vec (n + 1) → ℝ≥0∞ :=
    (positiveOrthant (n + 1)).indicator (fun x ↦ ENNReal.ofReal (Real.exp (-scoreSum x)))
  let f : Vec (n + 1) → ℝ≥0∞ := fun x ↦ d x * g (fun i ↦ x i / scoreSum x)
  have hd : Measurable d := ((measurable_scoreSum _).neg.exp.ennreal_ofReal).indicator
    (measurableSet_positiveOrthant _)
  have hf : Measurable f := hd.mul (hg.comp (measurable_simplexNormalize _))
  have hpositive : MeasurableSet {x : Vec (n + 1) | 0 < scoreSum x} :=
    measurableSet_lt measurable_const (measurable_scoreSum _)
  have hrestrict : (∫⁻ x, f x) = ∫⁻ x in {x : Vec (n + 1) | 0 < scoreSum x}, f x := by
    rw [← lintegral_indicator hpositive]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ positiveOrthant (n + 1)
    · have hxs : x ∈ {x : Vec (n + 1) | 0 < scoreSum x} := sum_pos_of_mem_positiveOrthant hx
      rw [indicator_of_mem hxs]
    · have hzero : f x = 0 := by simp [f, d, indicator_of_notMem hx]
      by_cases hxs : x ∈ {x : Vec (n + 1) | 0 < scoreSum x}
      · rw [indicator_of_mem hxs]
      · rw [indicator_of_notMem hxs, hzero]
  rw [simplexLaw, lintegral_map hg (measurable_simplexNormalize _), expVectorMeasure, exp_pi_density_pos]
  change (∫⁻ x, g (fun i ↦ x i / scoreSum x) ∂volume.withDensity d) = _
  have hmg : Measurable (fun x : Vec (n + 1) ↦ g (fun i ↦ x i / scoreSum x)) :=
    hg.comp (measurable_simplexNormalize _)
  rw [lintegral_withDensity_eq_lintegral_mul volume hd hmg]
  change (∫⁻ x, f x) = _
  rw [hrestrict, lintegral_sum_pos_eq_radial hf]
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ),
          (ENNReal.ofReal (s ^ n) * ENNReal.ofReal (Real.exp (-s))) *
          (∫⁻ v in simplexTail n, g (completeSimplex v)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change (0 : ℝ) < s at hs
      change ENNReal.ofReal (s ^ n) * (∫⁻ v, f (s • completeSimplex v)) = _
      have hinner :
          (∫⁻ v, f (s • completeSimplex v)) =
          ENNReal.ofReal (Real.exp (-s)) * ∫⁻ v in simplexTail n, g (completeSimplex v) := by
        rw [← lintegral_indicator (measurableSet_simplexTail n)]
        have hmi : Measurable ((simplexTail n).indicator (fun v ↦ g (completeSimplex v))) :=
          (hg.comp measurable_completeSimplex).indicator (measurableSet_simplexTail n)
        rw [← lintegral_const_mul _ hmi]
        apply lintegral_congr
        intro v
        have hmem : s • completeSimplex v ∈ positiveOrthant (n + 1) ↔ v ∈ simplexTail n :=
          smul_mem_positiveOrthant hs _
        by_cases hv : v ∈ simplexTail n
        · change d (s • completeSimplex v) *
            g (fun i ↦ (s • completeSimplex v) i / scoreSum (s • completeSimplex v)) = _
          rw [normalize_completeSimplex hs]
          simp [d, indicator_of_mem hv, indicator_of_mem (hmem.mpr hv)]
        · simp [f, d, indicator_of_notMem hv, indicator_of_notMem (mt hmem.mp hv)]
      simp only [hinner, mul_assoc]
    _ = _ := by
      have hm : Measurable (fun s : ℝ ↦ ENNReal.ofReal (s ^ n) *
          ENNReal.ofReal (Real.exp (-s))) := by fun_prop
      rw [lintegral_mul_const _ hm, lintegral_gamma_nat]

/-- Integrate a cubical test function by radius and a uniform simplex direction. -/
theorem lintegral_cube_eq_simplex {n : ℕ} {f : Vec (n + 1) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x in cube (n + 1), f x) =
      ∫⁻ s in Ioi (0 : ℝ), (n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) *
        (∫⁻ u, (cube (n + 1)).indicator f (s • u) ∂simplexLaw (n + 1)) := by
  classical
  let F := (cube (n + 1)).indicator f
  let G := (positiveOrthant (n + 1)).indicator F
  have hc : MeasurableSet (cube (n + 1)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hF : Measurable F := hf.indicator hc
  have hG : Measurable G := hF.indicator (measurableSet_positiveOrthant _)
  have hpositive : MeasurableSet {x : Vec (n + 1) | 0 < scoreSum x} :=
    measurableSet_lt measurable_const (measurable_scoreSum _)
  have hnonzero : ∀ᵐ x : Vec (n + 1) ∂volume, ∀ i, x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact Measure.ae_eval_ne (fun _ ↦ volume) i 0
  have hFG : F =ᵐ[volume] G := by
    filter_upwards [hnonzero] with x hx
    by_cases hxc : x ∈ cube (n + 1)
    · have hxp : x ∈ positiveOrthant (n + 1) := by
        intro i
        exact lt_of_le_of_ne (mem_univ_pi.mp hxc i).1 (Ne.symm (hx i))
      exact (indicator_of_mem hxp F).symm
    · have hzero : F x = 0 := indicator_of_notMem hxc f
      by_cases hxp : x ∈ positiveOrthant (n + 1)
      · exact (indicator_of_mem hxp F).symm
      · exact hzero.trans (indicator_of_notMem hxp F).symm
  have hGpos : (∫⁻ x, G x) = ∫⁻ x in {x : Vec (n + 1) | 0 < scoreSum x}, G x := by
    rw [← lintegral_indicator hpositive]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ {x : Vec (n + 1) | 0 < scoreSum x}
    · rw [indicator_of_mem hx]
    · have hn : x ∉ positiveOrthant (n + 1) :=
        fun h ↦ hx (sum_pos_of_mem_positiveOrthant h)
      rw [indicator_of_notMem hx]
      exact indicator_of_notMem hn F
  rw [← lintegral_indicator hc]
  change (∫⁻ x, F x) = _
  rw [lintegral_congr_ae hFG, hGpos, lintegral_sum_pos_eq_radial hG]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  change 0 < s at hs
  change ENNReal.ofReal (s ^ n) * (∫⁻ v, G (s • completeSimplex v)) = _
  have hmeas : Measurable (fun u ↦ F (s • u)) := hF.comp (measurable_const_smul s)
  have hinner : (∫⁻ v, G (s • completeSimplex v)) =
      ∫⁻ v in simplexTail n, F (s • completeSimplex v) := by
    rw [← lintegral_indicator (measurableSet_simplexTail n)]
    apply lintegral_congr
    intro v
    have hm : s • completeSimplex v ∈ positiveOrthant (n + 1) ↔ v ∈ simplexTail n :=
      smul_mem_positiveOrthant hs _
    by_cases hv : v ∈ simplexTail n
    · simp [G, indicator_of_mem hv, indicator_of_mem (hm.mpr hv)]
    · simp [G, indicator_of_notMem hv, indicator_of_notMem (mt hm.mp hv)]
  have hfac0 : (n.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfactop : (n.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  change _ = (n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) *
    (∫⁻ u, F (s • u) ∂simplexLaw (n + 1))
  rw [hinner, lintegral_simplexLaw_eq hmeas]
  rw [mul_assoc, mul_left_comm _ (ENNReal.ofReal _), ENNReal.inv_mul_cancel_left hfac0 hfactop]


/-- Real cubical radial integration for a bounded nonnegative measurable test function. -/
theorem integral_cube_eq_simplex {n : ℕ} {f : Vec (n + 1) → ℝ}
    (hf : Measurable f) {B : ℝ}
    (hB : ∀ x ∈ cube (n + 1), 0 ≤ f x ∧ f x ≤ B) :
    (∫ x in cube (n + 1), f x) =
      ∫ s in Ioi (0 : ℝ), (n.factorial : ℝ)⁻¹ * s ^ n *
        (∫ u, (cube (n + 1)).indicator f (s • u) ∂simplexLaw (n + 1)) := by
  classical
  let F := (cube (n + 1)).indicator f
  let L (s : ℝ) := ∫⁻ u, ENNReal.ofReal (F (s • u)) ∂simplexLaw (n + 1)
  let H (s : ℝ) := (n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) * L s
  have hc : MeasurableSet (cube (n + 1)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hF : Measurable F := hf.indicator hc
  have hFnonneg (x : Vec (n + 1)) : 0 ≤ F x := by
    by_cases hx : x ∈ cube (n + 1)
    · rw [show F x = f x from indicator_of_mem hx _]
      exact (hB x hx).1
    · rw [show F x = 0 from indicator_of_notMem hx _]
  have hFle (x : Vec (n + 1)) : F x ≤ max 0 B := by
    by_cases hx : x ∈ cube (n + 1)
    · rw [show F x = f x from indicator_of_mem hx _]
      exact (hB x hx).2.trans (le_max_right _ _)
    · rw [show F x = 0 from indicator_of_notMem hx _]
      exact le_max_left _ _
  have hL : Measurable L := by
    have hm : Measurable (fun p : ℝ × Vec (n + 1) ↦ ENNReal.ofReal (F (p.1 • p.2))) :=
      (hF.comp (by fun_prop)).ennreal_ofReal
    exact hm.lintegral_prod_right'
  have hH : Measurable H := by
    have hpow : Measurable (fun s : ℝ ↦ ENNReal.ofReal (s ^ n)) := by fun_prop
    exact (measurable_const.mul hpow).mul hL
  have hLtop (s : ℝ) : L s < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono
      (g := fun _ ↦ ENNReal.ofReal (max 0 B))
      (fun u ↦ ENNReal.ofReal_le_ofReal (hFle (s • u)))) ?_
    simp
  have hHtop (s : ℝ) : H s < ⊤ := by
    have hfac : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    refine ENNReal.mul_lt_top ?_ (hLtop s)
    exact ENNReal.mul_lt_top ((ENNReal.inv_ne_top.mpr hfac).lt_top) ENNReal.ofReal_lt_top
  have hlin :
      (∫⁻ x in cube (n + 1), ENNReal.ofReal (f x)) = ∫⁻ s in Ioi (0 : ℝ), H s := by
    rw [lintegral_cube_eq_simplex hf.ennreal_ofReal]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _
    change (n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) *
        (∫⁻ u, (cube (n + 1)).indicator (fun x ↦ ENNReal.ofReal (f x)) (s • u)
          ∂simplexLaw (n + 1)) =
      (n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) * L s
    congr 1
    apply lintegral_congr
    intro u
    by_cases hx : s • u ∈ cube (n + 1)
    · rw [indicator_of_mem hx, show F (s • u) = f (s • u) from indicator_of_mem hx _]
    · rw [indicator_of_notMem hx, show F (s • u) = 0 from indicator_of_notMem hx _,
        ENNReal.ofReal_zero]
  have hnonneg : 0 ≤ᵐ[(volume : Measure (Vec (n + 1))).restrict (cube (n + 1))] f := by
    filter_upwards [ae_restrict_mem hc] with x hx
    exact (hB x hx).1
  calc
    _ = (∫⁻ x in cube (n + 1), ENNReal.ofReal (f x)).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnonneg hf.aestronglyMeasurable
    _ = (∫⁻ s in Ioi (0 : ℝ), H s).toReal := congrArg ENNReal.toReal hlin
    _ = ∫ s in Ioi (0 : ℝ), (H s).toReal :=
      (integral_toReal hH.aemeasurable (Eventually.of_forall hHtop)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change 0 < s at hs
      have hmean : (∫ u, F (s • u) ∂simplexLaw (n + 1)) = (L s).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Eventually.of_forall (fun u ↦ hFnonneg (s • u)))
          (hF.comp (measurable_const_smul s)).aestronglyMeasurable
      change ((n.factorial : ℝ≥0∞)⁻¹ * ENNReal.ofReal (s ^ n) * L s).toReal =
        (n.factorial : ℝ)⁻¹ * s ^ n * (∫ u, F (s • u) ∂simplexLaw (n + 1))
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le _),
        ENNReal.toReal_inv, ENNReal.toReal_natCast, ← hmean]

end

end SupercriticalLogRank
