module

public import SupercriticalLogRank.ColumnFactorization

@[expose] public section

/-! The exponential score transform and the integral for the stable diagonal matching. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SupercriticalLogRank

noncomputable def unitScoreMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitScoreMeasure := by
  constructor
  simp [unitScoreMeasure]

theorem exp_neg_map_expMeasure :
    (expMeasure 1).map (fun x : ℝ ↦ Real.exp (-x)) = unitScoreMeasure := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  have hmeas : Measurable (fun x : ℝ ↦ Real.exp (-x)) := by fun_prop
  let _ : IsProbabilityMeasure ((expMeasure 1).map (fun x : ℝ ↦ Real.exp (-x))) :=
    inferInstance
  apply Measure.ext_of_Ici
  intro t
  rw [Measure.map_apply hmeas measurableSet_Ici]
  by_cases ht : 0 < t
  · have hpre : (fun x : ℝ ↦ Real.exp (-x)) ⁻¹' Ici t = Iic (-Real.log t) := by
      ext x
      change t ≤ Real.exp (-x) ↔ x ≤ -Real.log t
      nth_rewrite 1 [← Real.exp_log ht]
      rw [Real.exp_le_exp]
      constructor <;> intro h <;> linarith
    have hint : Ici t ∩ Icc (0 : ℝ) 1 = Icc t 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ht.le.trans h.1, h.2⟩⟩
    rw [hpre, ← ofReal_cdf, cdf_expMeasure_eq zero_lt_one, unitScoreMeasure,
      Measure.restrict_apply measurableSet_Ici, hint, Real.volume_Icc]
    by_cases hle : t ≤ 1
    · have hl : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.le hle)
      simp [hl, Real.exp_log ht]
    · have hl : ¬ 0 ≤ -Real.log t :=
        not_le.mpr (neg_neg_of_pos (Real.log_pos (lt_of_not_ge hle)))
      simp [hl, ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_ge hle))]
  · have hpre : (fun x : ℝ ↦ Real.exp (-x)) ⁻¹' Ici t = univ := by
      ext x
      simp [show t ≤ Real.exp (-x) from (le_of_not_gt ht).trans (Real.exp_pos _).le]
    have hint : Ici t ∩ Icc (0 : ℝ) 1 = Icc 0 1 :=
      inter_eq_right.mpr (fun _ h ↦ (le_of_not_gt ht).trans h.1)
    rw [hpre, measure_univ, unitScoreMeasure, Measure.restrict_apply measurableSet_Ici, hint]
    simp

theorem unitScoreMeasure_Iio {s : ℝ} (hs' : s ≤ 1) :
    unitScoreMeasure (Iio s) = ENNReal.ofReal s := by
  have heq : Iio s ∩ Icc (0 : ℝ) 1 = Ico 0 s := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans hs'⟩⟩
  rw [unitScoreMeasure, Measure.restrict_apply measurableSet_Iio, heq, Real.volume_Ico, sub_zero]

noncomputable def pairScoreMeasure : Measure (ℝ × ℝ) := unitScoreMeasure.prod unitScoreMeasure

instance : IsProbabilityMeasure pairScoreMeasure := by
  unfold pairScoreMeasure
  infer_instance

def allowedScorePair (a x y : ℝ) : Set (ℝ × ℝ) :=
  (Iio (a * x) ×ˢ Iio (a * y))ᶜ

theorem measurableSet_allowedScorePair (a x y : ℝ) : MeasurableSet (allowedScorePair a x y) :=
  (measurableSet_Iio.prod measurableSet_Iio).compl

theorem pairScoreMeasure_allowedScorePair {a x y : ℝ} (ha : a ∈ Icc 0 1)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    pairScoreMeasure (allowedScorePair a x y) = ENNReal.ofReal (1 - a ^ 2 * x * y) := by
  have hax0 : 0 ≤ a * x := mul_nonneg ha.1 hx.1
  have hay0 : 0 ≤ a * y := mul_nonneg ha.1 hy.1
  have hax1 : a * x ≤ 1 := (mul_le_of_le_one_left hx.1 ha.2).trans hx.2
  have hay1 : a * y ≤ 1 := (mul_le_of_le_one_left hy.1 ha.2).trans hy.2
  have hprod : pairScoreMeasure (Iio (a * x) ×ˢ Iio (a * y)) =
      ENNReal.ofReal ((a * x) * (a * y)) := by
    rw [pairScoreMeasure, Measure.prod_prod, unitScoreMeasure_Iio hax1,
      unitScoreMeasure_Iio hay1, ENNReal.ofReal_mul hax0]
  rw [allowedScorePair, measure_compl (measurableSet_Iio.prod measurableSet_Iio)
    (measure_ne_top _ _), measure_univ, hprod, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (mul_nonneg hax0 hay0)]
  congr 1
  ring

abbrev PairIndex (n : ℕ) := Fin n × Fin n
abbrev OffIndex (n : ℕ) := {ij : PairIndex n // ij.1 ≠ ij.2}
abbrev ScoreSpace (n : ℕ) := (Vec n × Vec n) × (OffIndex n → ℝ × ℝ)

private def sideCoord (n : ℕ) : Bool × PairIndex n ≃ PairIndex n ⊕ PairIndex n where
  toFun := fun (b, ij) ↦ if b then Sum.inr ij else Sum.inl ij
  invFun := Sum.elim (false, ·) (true, ·)
  left_inv := by rintro ⟨_ | _, ij⟩ <;> rfl
  right_inv := by rintro (ij | ij) <;> rfl

private def diagCoord (n : ℕ) : {ij : PairIndex n // ij.1 = ij.2} ≃ Fin n where
  toFun := fun ij ↦ ij.val.1
  invFun := fun i ↦ ⟨(i, i), rfl⟩
  left_inv := by
    rintro ⟨⟨i, j⟩, hij⟩
    change i = j at hij
    subst j
    rfl
  right_inv := fun _ ↦ rfl

noncomputable def vectorScoreMeasure (n : ℕ) : Measure (Vec n) :=
  Measure.pi fun _ ↦ unitScoreMeasure

noncomputable def diagonalScoreMeasure (n : ℕ) : Measure (Vec n × Vec n) :=
  (vectorScoreMeasure n).prod (vectorScoreMeasure n)

noncomputable def offScoreMeasure (n : ℕ) : Measure (OffIndex n → ℝ × ℝ) :=
  Measure.pi fun _ ↦ pairScoreMeasure

instance (n : ℕ) : IsProbabilityMeasure (vectorScoreMeasure n) := by
  unfold vectorScoreMeasure
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (diagonalScoreMeasure n) := by
  unfold diagonalScoreMeasure
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (offScoreMeasure n) := by
  unfold offScoreMeasure
  infer_instance

private theorem measurePreserving_groupProfile (n : ℕ) :
    MeasurePreserving
      (fun (p : Profile n) (ij : PairIndex n) ↦ (p (false, ij), p (true, ij)))
      (Measure.pi fun _ ↦ unitScoreMeasure) (Measure.pi fun _ ↦ pairScoreMeasure) := by
  have h1 := measurePreserving_piCongrLeft (fun _ ↦ unitScoreMeasure) (sideCoord n)
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : PairIndex n ⊕ PairIndex n ↦ unitScoreMeasure)
  have h3 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (PairIndex n)
    (fun _ ↦ unitScoreMeasure) (fun _ ↦ unitScoreMeasure)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (PairIndex n))
  exact h3.comp (h2.comp h1)

private theorem measurePreserving_splitPairs (n : ℕ) :
    MeasurePreserving
      (fun p : PairIndex n → ℝ × ℝ ↦
        ((fun i : Fin n ↦ (p (i, i)).1, fun i : Fin n ↦ (p (i, i)).2),
          fun ij : OffIndex n ↦ p ij.val))
      (Measure.pi fun _ ↦ pairScoreMeasure)
      ((diagonalScoreMeasure n).prod (offScoreMeasure n)) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd
    (fun _ : PairIndex n ↦ pairScoreMeasure) (fun ij ↦ ij.1 = ij.2)
  have h2 := measurePreserving_piCongrLeft (fun _ ↦ pairScoreMeasure) (diagCoord n)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ ↦ unitScoreMeasure) (fun _ ↦ unitScoreMeasure)
  exact ((h3.comp h2).prod (MeasurePreserving.id (offScoreMeasure n))).comp h1

private theorem measurePreserving_profileScores (n : ℕ) :
    MeasurePreserving (fun (p : Profile n) i ↦ Real.exp (-p i)) (marketMeasure n)
      (Measure.pi fun _ ↦ unitScoreMeasure) := by
  refine ⟨by fun_prop, ?_⟩
  have hσ (_i : Bool × Fin n × Fin n) :
      SigmaFinite ((expMeasure 1).map (fun x : ℝ ↦ Real.exp (-x))) := by
    rw [exp_neg_map_expMeasure]
    infer_instance
  unfold marketMeasure
  rw [Measure.pi_map_pi (hμ := hσ) (fun _ ↦ (by fun_prop :
    Measurable (fun x : ℝ ↦ Real.exp (-x))).aemeasurable)]
  simp only [exp_neg_map_expMeasure]

noncomputable def splitScores (n : ℕ) (p : Profile n) :
    ScoreSpace n :=
  ((diagonalFirmScores p, diagonalWorkerScores p),
    fun ij ↦ (Real.exp (-p (false, ij.val)), Real.exp (-p (true, ij.val))))

theorem measurePreserving_splitScores (n : ℕ) :
    MeasurePreserving (splitScores n) (marketMeasure n)
      ((diagonalScoreMeasure n).prod (offScoreMeasure n)) :=
  (measurePreserving_splitPairs n).comp
    ((measurePreserving_groupProfile n).comp (measurePreserving_profileScores n))

def offAllowedSet {n : ℕ} (a : ℝ) (xy : Vec n × Vec n) :
    Set (OffIndex n → ℝ × ℝ) :=
  univ.pi (fun ij ↦ allowedScorePair a (xy.1 ij.val.1) (xy.2 ij.val.2))

noncomputable def offRestrictedScoreMeasure {n : ℕ} (a : ℝ) (xy : Vec n × Vec n) :
    Measure (OffIndex n → ℝ × ℝ) :=
  Measure.pi (fun ij ↦ pairScoreMeasure.restrict
    (allowedScorePair a (xy.1 ij.val.1) (xy.2 ij.val.2)))

theorem offRestrictedScoreMeasure_eq {n : ℕ} (a : ℝ) (xy : Vec n × Vec n) :
    offRestrictedScoreMeasure a xy = (offScoreMeasure n).restrict (offAllowedSet a xy) := by
  rw [offScoreMeasure, offAllowedSet, Measure.restrict_pi_pi]
  rfl

def stableScoreEvent (n : ℕ) (a : ℝ) :
    Set (ScoreSpace n) :=
  {w | w.2 ∈ offAllowedSet a w.1}

theorem measurableSet_stableScoreEvent (n : ℕ) (a : ℝ) :
    MeasurableSet (stableScoreEvent n a) := by
  have heq : stableScoreEvent n a =
      ⋂ ij : OffIndex n, {w : ScoreSpace n |
        ¬ ((w.2 ij).1 < a * w.1.1 ij.val.1 ∧ (w.2 ij).2 < a * w.1.2 ij.val.2)} := by
    ext w
    simp [stableScoreEvent, offAllowedSet, allowedScorePair]
  rw [heq]
  apply MeasurableSet.iInter
  intro ij
  have h1 : Measurable (fun w : ScoreSpace n ↦ (w.2 ij).1) := by fun_prop
  have h2 : Measurable (fun w : ScoreSpace n ↦ a * w.1.1 ij.val.1) := by fun_prop
  have h3 : Measurable (fun w : ScoreSpace n ↦ (w.2 ij).2) := by fun_prop
  have h4 : Measurable (fun w : ScoreSpace n ↦ a * w.1.2 ij.val.2) := by fun_prop
  exact ((measurableSet_lt h1 h2).inter (measurableSet_lt h3 h4)).compl

theorem exp_neg_lt_mul_exp_neg_iff (a b ε : ℝ) :
    Real.exp (-a) < Real.exp (-ε) * Real.exp (-b) ↔ b + ε < a := by
  rw [← Real.exp_add, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

theorem preimage_stableScoreEvent (n : ℕ) (ε : ℝ) :
    splitScores n ⁻¹' stableScoreEvent n (Real.exp (-ε)) = stableEvent n ε := by
  ext p
  simp only [mem_preimage, stableScoreEvent, offAllowedSet, mem_ofPred_eq, mem_pi,
    mem_univ, true_implies, allowedScorePair, mem_compl_iff, mem_prod, mem_Iio,
    splitScores, diagonalFirmScores, diagonalWorkerScores, exp_neg_lt_mul_exp_neg_iff,
    stableEvent]
  exact ⟨fun h i j hij ↦ h ⟨(i, j), hij⟩, fun h ij ↦ h ij.val.1 ij.val.2 ij.property⟩

theorem marketMeasure_stable_splitScores {n : ℕ} (ε : ℝ)
    {A : Set (ScoreSpace n)} (hA : MeasurableSet A) :
    marketMeasure n (stableEvent n ε ∩ splitScores n ⁻¹' A) =
      ∫⁻ xy, offRestrictedScoreMeasure (Real.exp (-ε)) xy (Prod.mk xy ⁻¹' A)
        ∂diagonalScoreMeasure n := by
  rw [← preimage_stableScoreEvent, ← preimage_inter,
    (measurePreserving_splitScores n).measure_preimage
      ((measurableSet_stableScoreEvent n _).inter hA).nullMeasurableSet,
    Measure.prod_apply ((measurableSet_stableScoreEvent n _).inter hA)]
  apply lintegral_congr
  intro xy
  rw [offRestrictedScoreMeasure_eq, Measure.restrict_apply (hA.preimage measurable_prodMk_left)]
  congr 1
  ext p
  simp only [mem_preimage, mem_inter_iff, stableScoreEvent, mem_ofPred_eq]
  exact and_comm

theorem vectorScoreMeasure_eq_restrict (n : ℕ) :
    vectorScoreMeasure n = volume.restrict (cube n) := by
  rw [cube, volume_pi, Measure.restrict_pi_pi]
  rfl

theorem diagonalScoreMeasure_eq_restrict (n : ℕ) :
    diagonalScoreMeasure n = volume.restrict (cube n ×ˢ cube n) := by
  rw [diagonalScoreMeasure, vectorScoreMeasure_eq_restrict, Measure.prod_restrict]
  rfl

theorem ae_diagonalScoreMeasure_mem (n : ℕ) :
    ∀ᵐ xy ∂diagonalScoreMeasure n, xy ∈ cube n ×ˢ cube n := by
  rw [diagonalScoreMeasure_eq_restrict]
  exact ae_restrict_mem ((measurableSet_cube n).prod (measurableSet_cube n))

private theorem kernelFactor_nonneg {q x y : ℝ} (hq : q ∈ Icc 0 1)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) : 0 ≤ 1 - q * x * y :=
  sub_nonneg.mpr ((mul_le_of_le_one_left hy.1 ((mul_le_of_le_one_left hx.1 hq.2).trans hx.2)).trans hy.2)

theorem stabilityKernel_nonneg_of_mem {n : ℕ} {q : ℝ} {x y : Vec n}
    (hq : q ∈ Icc 0 1) (hx : x ∈ cube n) (hy : y ∈ cube n) :
    0 ≤ stabilityKernel q x y := by
  unfold stabilityKernel
  refine Finset.prod_nonneg fun i _ ↦ Finset.prod_nonneg fun j _ ↦
    kernelFactor_nonneg hq ((mem_pi.mp hx) i (mem_univ _)) ((mem_pi.mp hy) j (mem_univ _))

theorem offRestrictedScoreMeasure_univ {n : ℕ} {a : ℝ} {xy : Vec n × Vec n}
    (ha : a ∈ Icc 0 1) (hxy : xy ∈ cube n ×ˢ cube n) :
    offRestrictedScoreMeasure a xy univ = ENNReal.ofReal (stabilityKernel (a ^ 2) xy.1 xy.2) := by
  have hq : a ^ 2 ∈ Icc 0 1 := ⟨sq_nonneg a, by nlinarith [ha.1, ha.2, mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]⟩
  have hx (i : Fin n) : xy.1 i ∈ Icc 0 1 := (mem_pi.mp hxy.1) i (mem_univ _)
  have hy (j : Fin n) : xy.2 j ∈ Icc 0 1 := (mem_pi.mp hxy.2) j (mem_univ _)
  have hreindex :
      (∏ ij : OffIndex n, (1 - a ^ 2 * xy.1 ij.val.1 * xy.2 ij.val.2)) =
        stabilityKernel (a ^ 2) xy.1 xy.2 := by
    rw [← Finset.prod_subtype
      (Finset.univ.filter fun ij : PairIndex n ↦ ij.1 ≠ ij.2) (by simp)
      (fun ij ↦ 1 - a ^ 2 * xy.1 ij.1 * xy.2 ij.2)]
    unfold stabilityKernel
    exact Finset.prod_finset_product' _ _ _ (by intro ij; simp [ne_comm])
      (f := fun i j ↦ 1 - a ^ 2 * xy.1 i * xy.2 j)
  rw [offRestrictedScoreMeasure, Measure.pi_univ]
  simp_rw [Measure.restrict_apply_univ,
    pairScoreMeasure_allowedScorePair ha (hx _) (hy _)]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun ij _ ↦ kernelFactor_nonneg hq (hx ij.val.1) (hy ij.val.2)), hreindex]

theorem marketMeasure_stable_diagonal {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    {A : Set (Vec n × Vec n)} (hA : MeasurableSet A) :
    marketMeasure n (stableEvent n ε ∩
      (fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' A) =
      ∫⁻ xy in A, ENNReal.ofReal (stabilityKernel ((Real.exp (-ε)) ^ 2) xy.1 xy.2)
        ∂diagonalScoreMeasure n := by
  have hpre : splitScores n ⁻¹' (A ×ˢ (univ : Set (OffIndex n → ℝ × ℝ))) =
      (fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' A := by
    ext p
    simp [splitScores]
  have ha : Real.exp (-ε) ∈ Icc 0 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hε)⟩
  rw [← hpre, marketMeasure_stable_splitScores ε (hA.prod MeasurableSet.univ),
    ← lintegral_indicator hA]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalScoreMeasure_mem n] with xy hxy
  by_cases hxyA : xy ∈ A
  · have hs : Prod.mk xy ⁻¹' (A ×ˢ (univ : Set (OffIndex n → ℝ × ℝ))) = univ := by
      ext w
      simp [hxyA]
    rw [hs, indicator_of_mem hxyA, offRestrictedScoreMeasure_univ ha hxy]
  · have hs : Prod.mk xy ⁻¹' (A ×ˢ (univ : Set (OffIndex n → ℝ × ℝ))) = ∅ := by
      ext w
      simp [hxyA]
    rw [hs, indicator_of_notMem hxyA, measure_empty]

theorem continuous_stabilityKernel (n : ℕ) (q : ℝ) :
    Continuous (fun xy : Vec n × Vec n ↦ stabilityKernel q xy.1 xy.2) := by
  unfold stabilityKernel
  fun_prop

theorem exp_neg_sq (ε : ℝ) : (Real.exp (-ε)) ^ 2 = Real.exp (-2 * ε) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem diagonalScoreMeasure_restrict_prod {n : ℕ} {A B : Set (Vec n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (diagonalScoreMeasure n).restrict (A ×ˢ B) =
      ((volume : Measure (Vec n)).restrict (cube n ∩ A)).prod
        (volume.restrict (cube n ∩ B)) := by
  rw [diagonalScoreMeasure_eq_restrict, Measure.restrict_restrict (hA.prod hB),
    prod_inter_prod, inter_comm A, inter_comm B]
  change ((volume : Measure (Vec n)).prod (volume : Measure (Vec n))).restrict _ = _
  rw [← Measure.prod_restrict]

theorem marketMeasure_stable_diagonalProd {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    {A B : Set (Vec n)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    marketMeasure n (stableEvent n ε ∩
      (fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' (A ×ˢ B)) =
      ∫⁻ x in cube n ∩ A, ∫⁻ y in cube n ∩ B,
        ENNReal.ofReal (stabilityKernel (Real.exp (-2 * ε)) x y) := by
  rw [marketMeasure_stable_diagonal ε hε (hA.prod hB),
    diagonalScoreMeasure_restrict_prod hA hB, exp_neg_sq]
  exact lintegral_prod _ (continuous_stabilityKernel n _).measurable.ennreal_ofReal.aemeasurable

theorem marketMeasure_real_stable_diagonalProd {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    {A B : Set (Vec n)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (marketMeasure n).real (stableEvent n ε ∩
      (fun p ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹' (A ×ˢ B)) =
      ∫ x in cube n ∩ A, ∫ y in cube n ∩ B, stabilityKernel (Real.exp (-2 * ε)) x y := by
  let q := Real.exp (-2 * ε)
  let f := fun xy : Vec n × Vec n ↦ stabilityKernel q xy.1 xy.2
  let μ := ((volume : Measure (Vec n)).restrict (cube n ∩ A)).prod
    (volume.restrict (cube n ∩ B))
  have hq : q ∈ Icc 0 1 := ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hf : Continuous f := continuous_stabilityKernel n q
  have hc : IsCompact (cube n) := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hμ : μ = (volume : Measure (Vec n × Vec n)).restrict
      ((cube n ∩ A) ×ˢ (cube n ∩ B)) := by
    change ((volume : Measure (Vec n)).restrict (cube n ∩ A)).prod
      (volume.restrict (cube n ∩ B)) = _
    rw [Measure.prod_restrict]
    rfl
  have hi : Integrable f μ := by
    rw [hμ]
    exact (hf.continuousOn.integrableOn_compact (hc.prod hc)).mono_set
      (Set.prod_mono inter_subset_left inter_subset_left)
  have hnon : 0 ≤ᵐ[μ] f := by
    rw [hμ]
    filter_upwards [ae_restrict_mem
      (((measurableSet_cube n).inter hA).prod ((measurableSet_cube n).inter hB))] with xy hxy
    exact stabilityKernel_nonneg_of_mem hq hxy.1.1 hxy.2.1
  rw [measureReal_def, marketMeasure_stable_diagonal ε hε (hA.prod hB),
    diagonalScoreMeasure_restrict_prod hA hB, exp_neg_sq]
  calc
    (∫⁻ xy, ENNReal.ofReal (f xy) ∂μ).toReal = ∫ xy, f xy ∂μ :=
      (integral_eq_lintegral_of_nonneg_ae hnon hf.measurable.aestronglyMeasurable).symm
    _ = _ := integral_prod _ hi

theorem marketMeasure_real_stable_firmScoreCutoff (n : ℕ) (ε c : ℝ) (hε : 0 ≤ ε) :
    (marketMeasure n).real (stableEvent n ε ∩ {p | scoreSum (diagonalFirmScores p) ≤ c}) =
      ∫ x in cube n ∩ {x | scoreSum x ≤ c}, ∫ y in cube n,
        stabilityKernel (Real.exp (-2 * ε)) x y := by
  have heq : (fun p : Profile n ↦ (diagonalFirmScores p, diagonalWorkerScores p)) ⁻¹'
      ({x : Vec n | scoreSum x ≤ c} ×ˢ (univ : Set (Vec n))) =
      {p | scoreSum (diagonalFirmScores p) ≤ c} := by
    ext p
    simp
  rw [← heq]
  simpa only [inter_univ] using
    marketMeasure_real_stable_diagonalProd ε hε
      (A := {x : Vec n | scoreSum x ≤ c}) (B := univ)
      (measurableSet_le (measurable_scoreSum n) measurable_const) MeasurableSet.univ

theorem marketMeasure_real_stable_integral (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (marketMeasure n).real (stableEvent n ε) =
      ∫ x in cube n, ∫ y in cube n, stabilityKernel (Real.exp (-2 * ε)) x y := by
  simpa only [prod_univ, univ_prod_univ, preimage_univ, inter_univ] using
    marketMeasure_real_stable_diagonalProd (n := n) ε hε
      (A := univ) (B := univ) MeasurableSet.univ MeasurableSet.univ

private def marketSwapIndex (n : ℕ) :
    Bool × Fin n × Fin n ≃ Bool × Fin n × Fin n where
  toFun := fun (b, i, j) ↦ (!b, j, i)
  invFun := fun (b, i, j) ↦ (!b, j, i)
  left_inv := by rintro ⟨_ | _, i, j⟩ <;> rfl
  right_inv := by rintro ⟨_ | _, i, j⟩ <;> rfl

private def marketSwap (n : ℕ) (p : Profile n) : Profile n :=
  p ∘ marketSwapIndex n

private theorem marketSwap_measurePreserving (n : ℕ) :
    MeasurePreserving (marketSwap n) (marketMeasure n) (marketMeasure n) := by
  let := isProbabilityMeasure_expMeasure (r := 1) zero_lt_one
  unfold marketMeasure
  convert measurePreserving_piCongrLeft (fun _ ↦ expMeasure 1) (marketSwapIndex n) using 1
  ext p ⟨b, i, j⟩
  cases b <;> rfl

private theorem marketSwap_mem_stableEvent (n : ℕ) (ε : ℝ) (p : Profile n) :
    marketSwap n p ∈ stableEvent n ε ↔ p ∈ stableEvent n ε := by
  simp only [stableEvent, mem_ofPred_eq, marketSwap, Function.comp_apply]
  change (∀ i j : Fin n, i ≠ j → ¬ (p (true, i, i) + ε < p (true, j, i) ∧
    p (false, j, j) + ε < p (false, j, i))) ↔
    ∀ i j : Fin n, i ≠ j → ¬ (p (false, i, i) + ε < p (false, i, j) ∧
      p (true, j, j) + ε < p (true, i, j))
  constructor <;> intro h i j hij hblock <;> exact h j i hij.symm hblock.symm

theorem marketMeasure_real_stable_workerScoreCutoff_eq_firm (n : ℕ) (ε c : ℝ) :
    (marketMeasure n).real (stableEvent n ε ∩ {p | scoreSum (diagonalWorkerScores p) ≤ c}) =
      (marketMeasure n).real (stableEvent n ε ∩ {p | scoreSum (diagonalFirmScores p) ≤ c}) := by
  have hm : Measurable (diagonalWorkerScores (n := n)) := by
    unfold diagonalWorkerScores
    fun_prop
  have hA : MeasurableSet (stableEvent n ε ∩
      {p | scoreSum (diagonalWorkerScores p) ≤ c}) :=
    (measurableSet_stableEvent n ε).inter
      (measurableSet_le ((measurable_scoreSum n).comp hm) measurable_const)
  have heq : marketSwap n ⁻¹' (stableEvent n ε ∩
      {p | scoreSum (diagonalWorkerScores p) ≤ c}) =
      stableEvent n ε ∩ {p | scoreSum (diagonalFirmScores p) ≤ c} := by
    ext p
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, marketSwap_mem_stableEvent]
    rfl
  have hmeasure := (marketSwap_measurePreserving n).measure_preimage hA.nullMeasurableSet
  rw [heq] at hmeasure
  exact congrArg ENNReal.toReal hmeasure.symm

theorem conditionedMarket_real_workerScoreCutoff_eq_firm (n : ℕ) (ε c : ℝ) :
    (conditionedMarket n ε).real {p | scoreSum (diagonalWorkerScores p) ≤ c} =
      (conditionedMarket n ε).real {p | scoreSum (diagonalFirmScores p) ≤ c} := by
  rw [conditionedMarket_real, conditionedMarket_real,
    marketMeasure_real_stable_workerScoreCutoff_eq_firm]

end SupercriticalLogRank
