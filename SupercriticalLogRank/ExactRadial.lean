module

public import SupercriticalLogRank.ColumnFactorization
public import SupercriticalLogRank.GlobalBound
public import SupercriticalLogRank.Radial
public import SupercriticalLogRank.SimplexConcentration

@[expose] public section

/-! The exact radial identity for a score cutoff. -/

namespace SupercriticalLogRank

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measurable_integratedKernel (n : ℕ) (q : ℝ) :
    Measurable (fun x : Vec n ↦ ∫ y in cube n, stabilityKernel q x y) := by
  have h : Measurable (fun p : Vec n × Vec n ↦ stabilityKernel q p.1 p.2) := by
    unfold stabilityKernel
    fun_prop (disch := exact measurable_pi_apply _)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem integratedKernel_nonneg {n : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    {x : Vec n} (hx : x ∈ cube n) :
    0 ≤ ∫ y in cube n, stabilityKernel q x y := by
  apply setIntegral_nonneg (measurableSet_cube n)
  intro y hy
  unfold stabilityKernel
  apply Finset.prod_nonneg
  intro i _
  apply Finset.prod_nonneg
  intro j _
  have hxi : x i ∈ Icc (0 : ℝ) 1 := hx i (mem_univ _)
  have hyj : y j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ _)
  exact sub_nonneg.mpr
    ((mul_le_of_le_one_right (mul_nonneg hq.1 hxi.1) hyj.2).trans
      ((mul_le_of_le_one_right hq.1 hxi.2).trans hq.2))

private theorem integratedKernel_le_one {n : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    {x : Vec n} (hx : x ∈ cube n) :
    (∫ y in cube n, stabilityKernel q x y) ≤ 1 := by
  have hvol : (volume : Measure (Vec n)) (cube n) = 1 := by
    rw [cube, volume_pi, Measure.pi_pi]
    simp [Real.volume_Icc]
  let : IsProbabilityMeasure ((volume : Measure (Vec n)).restrict (cube n)) := ⟨by simp [hvol]⟩
  have hb : ∀ᵐ y ∂(volume.restrict (cube n)), stabilityKernel q x y ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cube n)] with y hy
    unfold stabilityKernel
    have hfactor (i j : Fin n) : 1 - q * x i * y j ∈ Icc (0 : ℝ) 1 := by
      have hxi : x i ∈ Icc (0 : ℝ) 1 := hx i (mem_univ _)
      have hyj : y j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ _)
      refine ⟨sub_nonneg.mpr ?_, sub_le_self _ (mul_nonneg (mul_nonneg hq.1 hxi.1) hyj.1)⟩
      exact (mul_le_of_le_one_right (mul_nonneg hq.1 hxi.1) hyj.2).trans
        ((mul_le_of_le_one_right hq.1 hxi.2).trans hq.2)
    have hcol (i : Fin n) : (∏ j ∈ Finset.univ.erase i, (1 - q * x i * y j)) ∈ Icc (0 : ℝ) 1 :=
      ⟨Finset.prod_nonneg (fun j _ ↦ (hfactor i j).1),
        Finset.prod_le_one₀ (fun j _ ↦ (hfactor i j).1) (fun j _ ↦ (hfactor i j).2)⟩
    exact ⟨Finset.prod_nonneg (fun i _ ↦ (hcol i).1),
      Finset.prod_le_one₀ (fun i _ ↦ (hcol i).1) (fun i _ ↦ (hcol i).2)⟩
  calc
    _ ≤ ∫ _y in cube n, (1 : ℝ) := integral_mono_of_nonneg
      (hb.mono fun _ h ↦ h.1) (integrable_const _) (hb.mono fun _ h ↦ h.2)
    _ = 1 := by simp

private theorem scale_factor {n : ℕ} {q s : ℝ} (hs : s ≠ 0) :
    (s ^ n) * ((q * s)⁻¹ ^ (n + 1)) = q⁻¹ ^ (n + 1) / s := by
  calc
    _ = q⁻¹ ^ (n + 1) * (s ^ n * s⁻¹ ^ n) * s⁻¹ := by
      rw [mul_inv, mul_pow, pow_succ s⁻¹]
      ring
    _ = _ := by
      have hsp : s ^ n * s⁻¹ ^ n = 1 := by
        rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]
      rw [hsp, mul_one, div_eq_mul_inv]

private def cutKernel {n : ℕ} (q c : ℝ) (x : Vec n) : ℝ :=
  ({z : Vec n | scoreSum z ≤ c} : Set (Vec n)).indicator
    (fun z ↦ ∫ y in cube n, stabilityKernel q z y) x

private theorem measurable_cutKernel {n : ℕ} (q c : ℝ) :
    Measurable (cutKernel (n := n) q c) :=
  (measurable_integratedKernel n q).indicator
    (measurableSet_le (measurable_scoreSum n) measurable_const)

private theorem integral_cutKernel_smul {n : ℕ} (hn : 0 < n) {q s c : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) :
    (∫ u, (cube n).indicator (cutKernel q c) (s • u) ∂simplexLaw n) =
      if s ≤ c then (q * s)⁻¹ ^ n * radialDensity n q s else 0 := by
  classical
  have hqs : q * s ≠ 0 := (mul_pos hq.1 hs).ne'
  have hidentity : ∀ᵐ u ∂simplexLaw n,
      (cube n).indicator (cutKernel q c) (s • u) =
        if s ≤ c then (q * s)⁻¹ ^ n * radialWeight n q s u else 0 := by
    filter_upwards [ae_simplexLaw n hn] with u hu
    have hsum : scoreSum (s • u) = s := by rw [scoreSum_smul, hu.2, mul_one]
    by_cases hc : s ≤ c
    · by_cases hcube : s • u ∈ cube n
      · simp [cutKernel, hsum, hc, hcube, radialWeight, integral_stabilityKernel_radial hqs]
      · simp [hc, hcube, radialWeight]
    · simp [cutKernel, hsum, hc]
  rw [integral_congr_ae hidentity]
  split_ifs
  · rw [integral_const_mul]
    rfl
  · simp

private theorem integral_cutKernel_eq_inter {n : ℕ} (q c : ℝ) :
    (∫ x in cube n, cutKernel q c x) =
      ∫ x in cube n ∩ {x : Vec n | scoreSum x ≤ c}, ∫ y in cube n, stabilityKernel q x y := by
  have hc : MeasurableSet {x : Vec n | scoreSum x ≤ c} :=
    measurableSet_le (measurable_scoreSum n) measurable_const
  unfold cutKernel
  rw [integral_indicator hc, Measure.restrict_restrict hc, Set.inter_comm]

private theorem integrate_radial_cutoff (n : ℕ) {q c : ℝ} (hq : q ∈ Ioc (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), (n.factorial : ℝ)⁻¹ * s ^ n *
      (∫ u, (cube (n + 1)).indicator (cutKernel q c) (s • u) ∂simplexLaw (n + 1))) =
      q⁻¹ ^ (n + 1) / (n.factorial : ℝ) *
        ∫ s in Icc 0 c, radialDensity (n + 1) q s / s := by
  classical
  have hfun : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (n.factorial : ℝ)⁻¹ * s ^ n *
        (∫ u, (cube (n + 1)).indicator (cutKernel q c) (s • u) ∂simplexLaw (n + 1)) =
        (Iic c).indicator (fun v ↦
          q⁻¹ ^ (n + 1) / (n.factorial : ℝ) * (radialDensity (n + 1) q v / v)) s := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    have hsp : 0 < s := hs
    rw [integral_cutKernel_smul (Nat.succ_pos _) hq hsp]
    by_cases hsc : s ≤ c
    · simp only [hsc, ite_true, mem_Iic, indicator_of_mem]
      calc
        _ = (s ^ n * ((q * s)⁻¹ ^ (n + 1))) *
            radialDensity (n + 1) q s / (n.factorial : ℝ) := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ = _ := by
          rw [scale_factor hsp.ne']
          simp only [div_eq_mul_inv]
          ac_rfl
    · simp [hsc]
  have hset : Iic c ∩ Ioi (0 : ℝ) = Ioc 0 c := by
    ext s
    simp [and_comm]
  rw [integral_congr_ae hfun, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hset, integral_const_mul,
    integral_Icc_eq_integral_Ioc]

theorem integral_scoreKernel_eq_radial (n : ℕ) {q c : ℝ} (hq : q ∈ Ioc (0 : ℝ) 1) :
    (∫ x in cube (n + 1) ∩ {x : Vec (n + 1) | scoreSum x ≤ c},
      ∫ y in cube (n + 1), stabilityKernel q x y) =
        q⁻¹ ^ (n + 1) / (n.factorial : ℝ) *
          ∫ s in Icc 0 c, radialDensity (n + 1) q s / s := by
  rw [← integral_cutKernel_eq_inter, integral_cube_eq_simplex (measurable_cutKernel q c)
    (B := 1), integrate_radial_cutoff n hq]
  intro x hx
  have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  by_cases hxc : scoreSum x ≤ c
  · rw [cutKernel, indicator_of_mem (show x ∈ {z : Vec (n + 1) | scoreSum z ≤ c} from hxc)]
    exact ⟨integratedKernel_nonneg hq' hx, integratedKernel_le_one hq' hx⟩
  · simp [cutKernel, hxc]

end

end SupercriticalLogRank
