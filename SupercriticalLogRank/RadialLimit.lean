module

public import Mathlib

@[expose] public section

/-! The radial density estimates imply the log-score CDF by dominated convergence. -/

namespace SupercriticalLogRank

open Filter MeasureTheory Set
open scoped Topology

/-- Dominated convergence for a flat interior density, with an exponential bound on the
negative half-line. The values of the density at the two limiting endpoints are immaterial. -/
theorem logCoordinate_mass_limit (g : ℕ → ℝ → ℝ) (ρ t : ℝ)
    (hρt : ρ ≤ t) (ht : t ≤ 1)
    (hg : ∀ n, Measurable (g n))
    (h_nonneg : ∀ n x, 0 ≤ g n x)
    (h_upper : ∀ n x, g n x ≤ Real.exp 2)
    (h_left : ∀ n x, x < 0 → g n x ≤ Real.exp x)
    (h_below : ∀ x, x < ρ → Tendsto (fun n ↦ g n x) atTop (𝓝 0))
    (h_inside : ∀ x, ρ < x → x < 1 → Tendsto (fun n ↦ g n x) atTop (𝓝 (Real.exp (-1)))) :
    Tendsto (fun n ↦ ∫ x in Iic t, g n x) atTop (𝓝 ((t - ρ) * Real.exp (-1))) := by
  let bound : ℝ → ℝ :=
    fun x ↦ Real.exp x + (Icc 0 t).indicator (fun _ ↦ Real.exp 2) x
  let f : ℝ → ℝ := (Ioi ρ).indicator (fun _ ↦ Real.exp (-1))
  have h_bound_int : Integrable bound (volume.restrict (Iic t)) := by
    refine (integrableOn_exp_Iic t).add ?_
    have hc : IntegrableOn (fun _ : ℝ ↦ Real.exp 2) (Icc 0 t) volume :=
      integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact (hc.integrable_indicator measurableSet_Icc).restrict
  have h_dom (n : ℕ) : ∀ᵐ x ∂volume.restrict (Iic t), ‖g n x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (h_nonneg n x)]
    by_cases hx₀ : x < 0
    · have hnot : x ∉ Icc (0 : ℝ) t := fun h ↦ hx₀.not_ge h.1
      simp only [bound, Set.indicator_of_notMem hnot, add_zero]
      exact h_left n x hx₀
    · have hmem : x ∈ Icc (0 : ℝ) t := ⟨le_of_not_gt hx₀, hx⟩
      simp only [bound, Set.indicator_of_mem hmem]
      exact (h_upper n x).trans (le_add_of_nonneg_left (Real.exp_nonneg x))
  have h_lim : ∀ᵐ x ∂volume.restrict (Iic t), Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic,
      (volume.restrict (Iic t)).ae_ne ρ, (volume.restrict (Iic t)).ae_ne 1] with x hx hneρ hne1
    have hx1 : x < 1 := lt_of_le_of_ne (hx.trans ht) hne1
    by_cases hxr : x < ρ
    · have hnot : x ∉ Ioi ρ := hxr.le.not_gt
      simpa only [f, Set.indicator_of_notMem hnot] using h_below x hxr
    · have hrx : ρ < x := lt_of_le_of_ne (le_of_not_gt hxr) hneρ.symm
      have hmem : x ∈ Ioi ρ := hrx
      simpa only [f, Set.indicator_of_mem hmem] using h_inside x hrx hx1
  have h_eval : (∫ x in Iic t, f x) = (t - ρ) * Real.exp (-1) := by
    simp only [f]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    change (∫ _ in Ioc ρ t, Real.exp (-1)) = _
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hρt)]
    rfl
  rw [← h_eval]
  exact tendsto_integral_of_dominated_convergence bound
    (fun n ↦ (hg n).aestronglyMeasurable) h_bound_int h_dom h_lim

/-- The logarithm of the positive size `n+2`. -/
noncomputable def logMarketSize (n : ℕ) : ℝ :=
  Real.log ((n + 2 : ℕ) : ℝ)

private theorem logMarketSize_pos (n : ℕ) : 0 < logMarketSize n :=
  Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega))

private theorem logMarketSize_tendsto : Tendsto logMarketSize atTop atTop :=
  Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2))

private theorem marketSize_mul_log_ge_one (n : ℕ) :
    1 ≤ ((n + 2 : ℕ) : ℝ) * logMarketSize n := by
  have hN : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at h ⊢
    exact h
  have hlogN : (1 / 2 : ℝ) ≤ logMarketSize n :=
    hlog.trans (Real.log_le_log (by norm_num) hN)
  calc
    1 = (2 : ℝ) * (1 / 2) := by norm_num
    _ ≤ ((n + 2 : ℕ) : ℝ) * logMarketSize n :=
      mul_le_mul hN hlogN (by norm_num) (by positivity)

private theorem q_mul_log_coordinate (q : ℝ) (hq : 0 < q) (n : ℕ) (x : ℝ) :
    q * Real.exp (x * logMarketSize n) =
      Real.exp ((x - (-Real.log q / logMarketSize n)) * logMarketSize n) := by
  have hL : logMarketSize n ≠ 0 := (logMarketSize_pos n).ne'
  calc
    q * Real.exp (x * logMarketSize n) = Real.exp (Real.log q + x * logMarketSize n) := by
      rw [Real.exp_add, Real.exp_log hq]
    _ = _ := by congr 1; field_simp; ring

/-- The mass integral of a radial density in normalized log coordinates. -/
noncomputable def radialLogMass (H : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Iic t, H n (Real.exp (x * logMarketSize n))

/-- The global envelope and the asymptotic density on each interior window
determine the limiting radial mass at any score cutoff in `[ρ,1]`. -/
theorem radialLogMass_tendsto (H : ℕ → ℝ → ℝ) (q : ℕ → ℝ) (ρ t : ℝ)
    (hρt : ρ ≤ t) (ht : t ≤ 1)
    (hq : ∀ n, q n ∈ Ioc 0 1)
    (hscale : Tendsto (fun n ↦ -Real.log (q n) / logMarketSize n) atTop (𝓝 ρ))
    (hH : ∀ n, Measurable (H n))
    (hnonneg : ∀ n s, 0 < s → 0 ≤ H n s)
    (hupper : ∀ n s, 0 < s → H n s ≤ Real.exp 2)
    (hsmall : ∀ n s, 0 < s → H n s ≤ (q n * s) ^ (n + 2))
    (hwindow : ∀ (δ : ℝ), 0 < δ → ∀ (η : ℝ), 0 < η → ∀ᶠ n in atTop, ∀ s : ℝ,
      ((n + 2 : ℕ) : ℝ) ^ δ / q n ≤ s →
      s ≤ ((n + 2 : ℕ) : ℝ) ^ (1 - δ) →
      |H n s - Real.exp (-1)| < η) :
    Tendsto (fun n ↦ radialLogMass H n t) atTop (𝓝 ((t - ρ) * Real.exp (-1))) := by
  let g : ℕ → ℝ → ℝ := fun n x ↦ H n (Real.exp (x * logMarketSize n))
  have h_left (n : ℕ) (x : ℝ) (hx : x < 0) : g n x ≤ Real.exp x := by
    refine (hsmall n _ (Real.exp_pos _)).trans ?_
    calc
      (q n * Real.exp (x * logMarketSize n)) ^ (n + 2) ≤
          Real.exp (x * logMarketSize n) ^ (n + 2) := by
        gcongr
        · exact mul_nonneg (hq n).1.le (Real.exp_nonneg _)
        · exact mul_le_of_le_one_left (Real.exp_nonneg _) (hq n).2
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * (x * logMarketSize n)) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp x := by
        apply Real.exp_le_exp.mpr
        calc
          ((n + 2 : ℕ) : ℝ) * (x * logMarketSize n) =
              (((n + 2 : ℕ) : ℝ) * logMarketSize n) * x := by ring
          _ ≤ 1 * x := mul_le_mul_of_nonpos_right (marketSize_mul_log_ge_one n) hx.le
          _ = x := one_mul _
  have h_below (x : ℝ) (hx : x < ρ) : Tendsto (fun n ↦ g n x) atTop (𝓝 0) := by
    let δ := (ρ - x) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hr : x + δ < ρ := by dsimp [δ]; linarith
    have hlt : ∀ᶠ n in atTop, x + δ < -Real.log (q n) / logMarketSize n :=
      (tendsto_order.1 hscale).1 _ hr
    have hdec : Tendsto (fun n ↦ Real.exp ((-δ) * logMarketSize n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <|
        (tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hδ)).2 logMarketSize_tendsto
    refine squeeze_zero' (Eventually.of_forall fun n ↦ hnonneg n _ (Real.exp_pos _)) ?_ hdec
    filter_upwards [hlt] with n hn
    refine (hsmall n _ (Real.exp_pos _)).trans ?_
    have hqsexp : q n * Real.exp (x * logMarketSize n) ≤ Real.exp ((-δ) * logMarketSize n) := by
      rw [q_mul_log_coordinate _ (hq n).1]
      exact Real.exp_le_exp.mpr <|
        mul_le_mul_of_nonneg_right (by linarith) (logMarketSize_pos n).le
    calc
      (q n * Real.exp (x * logMarketSize n)) ^ (n + 2) ≤
          (Real.exp ((-δ) * logMarketSize n)) ^ (n + 2) :=
        pow_le_pow_left₀ (mul_nonneg (hq n).1.le (Real.exp_nonneg _)) hqsexp _
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * ((-δ) * logMarketSize n)) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((-δ) * logMarketSize n) := by
        apply Real.exp_le_exp.mpr
        have hnN : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ n + 2 by omega)
        simpa only [one_mul] using
          mul_le_mul_of_nonpos_right hnN (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr hδ.le) (logMarketSize_pos n).le)
  have h_inside (x : ℝ) (hx : ρ < x) (hx1 : x < 1) :
      Tendsto (fun n ↦ g n x) atTop (𝓝 (Real.exp (-1))) := by
    let δ := min ((x - ρ) / 2) ((1 - x) / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hr : ρ < x - δ := by
      have := min_le_left ((x - ρ) / 2) ((1 - x) / 2)
      dsimp [δ]
      linarith
    have hxu : x ≤ 1 - δ := by
      have := min_le_right ((x - ρ) / 2) ((1 - x) / 2)
      dsimp [δ]
      linarith
    have hlt : ∀ᶠ n in atTop, -Real.log (q n) / logMarketSize n < x - δ :=
      (tendsto_order.1 hscale).2 _ hr
    refine Metric.tendsto_nhds.2 fun η hη ↦ ?_
    filter_upwards [hlt, hwindow δ hδ η hη] with n hn hw
    have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hlow : ((n + 2 : ℕ) : ℝ) ^ δ / q n ≤ Real.exp (x * logMarketSize n) := by
      apply (div_le_iff₀ (hq n).1).2
      rw [mul_comm (Real.exp _), q_mul_log_coordinate _ (hq n).1, Real.rpow_def_of_pos hN]
      exact Real.exp_le_exp.mpr (calc
        Real.log ((n + 2 : ℕ) : ℝ) * δ = δ * logMarketSize n := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (logMarketSize_pos n).le)
    have hup : Real.exp (x * logMarketSize n) ≤ ((n + 2 : ℕ) : ℝ) ^ (1 - δ) := by
      rw [Real.rpow_def_of_pos hN]
      exact Real.exp_le_exp.mpr (calc
        x * logMarketSize n ≤ (1 - δ) * logMarketSize n :=
          mul_le_mul_of_nonneg_right hxu (logMarketSize_pos n).le
        _ = _ := mul_comm _ _)
    rw [Real.dist_eq]
    exact hw _ hlow hup
  exact logCoordinate_mass_limit g ρ t hρt ht
    (fun n ↦ (hH n).comp (by fun_prop))
    (fun n x ↦ hnonneg n _ (Real.exp_pos _))
    (fun n x ↦ hupper n _ (Real.exp_pos _))
    h_left h_below h_inside

/-- Exponential substitution in the logarithmic radial integral. -/
theorem integral_radial_eq_log (H : ℝ → ℝ) (t L : ℝ) (hL : 0 < L) :
    (∫ s in Ioc 0 (Real.exp (t * L)), H s / s) =
      L * ∫ x in Iic t, H (Real.exp (x * L)) := by
  let f (x : ℝ) := Real.exp (x * L)
  let f' (x : ℝ) := Real.exp (x * L) * L
  have himg : f '' Iic t = Ioc 0 (Real.exp (t * L)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx hL.le)⟩
    · intro hy
      have hy₀ : 0 < y := hy.1
      have hlog : Real.log y ≤ t * L := by
        apply Real.exp_le_exp.mp
        rw [Real.exp_log hy₀]
        exact hy.2
      refine ⟨Real.log y / L, (div_le_iff₀ hL).mpr hlog, ?_⟩
      simp [f, div_mul_cancel₀ _ hL.ne', Real.exp_log hy₀]
  have hD : ∀ x ∈ Iic t, HasDerivWithinAt f (f' x) (Iic t) x := by
    intro x _
    simpa [f, f'] using (((hasDerivAt_id x).mul_const L).exp.hasDerivWithinAt (s := Iic t))
  have hi : InjOn f (Iic t) := by
    intro x _ y _ h
    have hxy : x * L = y * L := Real.exp_injective h
    exact (mul_right_cancel₀ hL.ne') hxy
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Iic hD hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [f, f', smul_eq_mul, abs_of_pos (mul_pos (Real.exp_pos _) hL)]
  field_simp [ne_of_gt (Real.exp_pos (x * L))]

/-- Exponential substitution with a power cutoff, including the full radial mass at `t = 1`. -/
theorem integral_radial_rpow_eq_log (H : ℝ → ℝ) (t N : ℝ) (hN : 1 < N) :
    (∫ s in Icc 0 (N ^ t), H s / s) =
      Real.log N * ∫ x in Iic t, H (Real.exp (x * Real.log N)) := by
  rw [← setIntegral_congr_set Ioc_ae_eq_Icc, Real.rpow_def_of_pos (by linarith : 0 < N),
    mul_comm (Real.log N) t]
  exact integral_radial_eq_log H t (Real.log N) (Real.log_pos hN)

/-- The common logarithmic factor in the radial mass and normalization cancels. -/
theorem radialMass_ratio_tendsto_of_log_mass (H : ℕ → ℝ → ℝ) (ρ t : ℝ) (hρ : ρ < 1)
    (hcut : Tendsto (fun n ↦ radialLogMass H n t) atTop (𝓝 ((t - ρ) * Real.exp (-1))))
    (htotal : Tendsto (fun n ↦ radialLogMass H n 1) atTop (𝓝 ((1 - ρ) * Real.exp (-1)))) :
    Tendsto (fun n : ℕ ↦
      (∫ s in Icc 0 (((n + 2 : ℕ) : ℝ) ^ t), H n s / s) /
      (∫ s in Icc 0 ((n + 2 : ℕ) : ℝ), H n s / s)) atTop (𝓝 ((t - ρ) / (1 - ρ))) := by
  have hlim := hcut.div htotal
    (mul_ne_zero (sub_ne_zero.mpr hρ.ne') (Real.exp_ne_zero _))
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)] at hlim
  refine hlim.congr' (Eventually.of_forall fun n ↦ ?_)
  have hN : 1 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < n + 2 by omega)
  have hc := integral_radial_rpow_eq_log (H n) t _ hN
  have hz := integral_radial_rpow_eq_log (H n) 1 _ hN
  rw [Real.rpow_one] at hz
  change radialLogMass H n t / radialLogMass H n 1 =
    (∫ s in Icc 0 (((n + 2 : ℕ) : ℝ) ^ t), H n s / s) /
    (∫ s in Icc 0 ((n + 2 : ℕ) : ℝ), H n s / s)
  rw [hc, hz]
  exact (mul_div_mul_left _ _ (logMarketSize_pos n).ne').symm

/-- Conditional score CDF limit from uniform interior density and a global envelope. -/
theorem radialMass_ratio_tendsto (H : ℕ → ℝ → ℝ) (q : ℕ → ℝ) (ρ t : ℝ)
    (hρt : ρ ≤ t) (ht : t ≤ 1) (hρ : ρ < 1)
    (hq : ∀ n, q n ∈ Ioc 0 1)
    (hscale : Tendsto (fun n ↦ -Real.log (q n) / logMarketSize n) atTop (𝓝 ρ))
    (hH : ∀ n, Measurable (H n))
    (hnonneg : ∀ n s, 0 < s → 0 ≤ H n s)
    (hupper : ∀ n s, 0 < s → H n s ≤ Real.exp 2)
    (hsmall : ∀ n s, 0 < s → H n s ≤ (q n * s) ^ (n + 2))
    (hwindow : ∀ (δ : ℝ), 0 < δ → ∀ (η : ℝ), 0 < η → ∀ᶠ n in atTop, ∀ s : ℝ,
      ((n + 2 : ℕ) : ℝ) ^ δ / q n ≤ s →
      s ≤ ((n + 2 : ℕ) : ℝ) ^ (1 - δ) →
      |H n s - Real.exp (-1)| < η) :
    Tendsto (fun n : ℕ ↦
      (∫ s in Icc 0 (((n + 2 : ℕ) : ℝ) ^ t), H n s / s) /
      (∫ s in Icc 0 ((n + 2 : ℕ) : ℝ), H n s / s)) atTop (𝓝 ((t - ρ) / (1 - ρ))) :=
  radialMass_ratio_tendsto_of_log_mass H ρ t hρ
    (radialLogMass_tendsto H q ρ t hρt ht hq hscale hH hnonneg hupper hsmall hwindow)
    (radialLogMass_tendsto H q ρ 1 hρ.le le_rfl hq hscale hH hnonneg hupper hsmall hwindow)

end SupercriticalLogRank
