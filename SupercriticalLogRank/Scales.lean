module

public import SupercriticalLogRank.Taylor

@[expose] public section

/-! The logarithmic cutoff and coefficient bounds on the interior radial window. -/

namespace SupercriticalLogRank

open Filter Set
open scoped Topology

/-- An upper bound on a typical simplex coordinate. -/
noncomputable def taylorM (x : ℝ) : ℝ := 4 * Real.log x / x

/-- The cutoff in the normalized column integral. -/
noncomputable def taylorL (x : ℝ) : ℝ := 8 * Real.log x

/-- Integrated second-order error at the chosen Taylor scale. -/
noncomputable def taylorError (x : ℝ) : ℝ :=
  columnError (taylorM x) (taylorL x)

private theorem eventually_large_taylorScale :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x :=
  (eventually_ge_atTop 1).and (Real.tendsto_log_atTop.eventually_ge_atTop 1)

private theorem taylorM_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ taylorM x := by
  unfold taylorM
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) (by linarith)

private theorem taylorL_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ taylorL x := by
  unfold taylorL
  exact mul_nonneg (by norm_num) (Real.log_nonneg hx)

private theorem taylorError_nonneg (x : ℝ) : 0 ≤ taylorError x := by
  exact columnError_nonneg _ _

private theorem sqrt_mul_taylorSmall_tendsto :
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (taylorM x * (1 + taylorL x) ^ 3))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x ^ (4 : ℕ) / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop 4 (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero
  refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hlog.const_mul (4 * 9 ^ 3))
  · filter_upwards [eventually_large_taylorScale] with x hx
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (taylorM_nonneg hx.1)
      (pow_nonneg (by linarith [taylorL_nonneg hx.1]) _))
  · filter_upwards [eventually_large_taylorScale] with x hx
    have hx₀ : 0 < x := by linarith [hx.1]
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx₀
    have hpow : (1 + 8 * Real.log x) ^ (3 : ℕ) ≤ (9 * Real.log x) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ (by linarith [hx.2]) (by linarith [hx.2]) _
    have heq : Real.sqrt x * (taylorM x * (1 + taylorL x) ^ 3)
        = (4 * Real.log x * (1 + 8 * Real.log x) ^ 3) / Real.sqrt x := by
      unfold taylorM taylorL
      field_simp
      rw [Real.sq_sqrt hx₀.le]
      ring
    rw [heq]
    calc
      _ ≤ (4 * Real.log x * (9 * Real.log x) ^ 3) / Real.sqrt x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by linarith [hx.2])) hs.le
      _ = _ := by ring

/-- The logarithmic truncation window is small compared to the maximum coordinate scale. -/
theorem taylorSmall_tendsto :
    Tendsto (fun x : ℝ ↦ taylorM x * (1 + taylorL x) ^ 3) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ sqrt_mul_taylorSmall_tendsto
  · filter_upwards [eventually_large_taylorScale] with x hx
    exact mul_nonneg (taylorM_nonneg hx.1) (pow_nonneg (by linarith [taylorL_nonneg hx.1]) _)
  · filter_upwards [eventually_large_taylorScale] with x hx
    exact le_mul_of_one_le_left
      (mul_nonneg (taylorM_nonneg hx.1) (pow_nonneg (by linarith [taylorL_nonneg hx.1]) _))
      (Real.one_le_sqrt.mpr hx.1)

/-- The sum of the integrated column errors tends to zero. -/
theorem taylorError_mul_tendsto :
    Tendsto (fun x : ℝ ↦ x * taylorError x) atTop (𝓝 0) := by
  have hsq := (sqrt_mul_taylorSmall_tendsto.pow 2).const_mul 7
  have htail := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul 16
  have hs := hsq.add htail
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_large_taylorScale] with x hx
  have hx₀ : 0 < x := by linarith [hx.1]
  have hexp : Real.exp (-taylorL x / 2) = (x ^ (4 : ℕ))⁻¹ := by
    rw [show -taylorL x / 2 = -((4 : ℕ) * Real.log x) by unfold taylorL; push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx₀]
  have hneg : x ^ (-(3 : ℝ)) = (x ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hx₀.le, Real.rpow_ofNat]
  change 7 * (Real.sqrt x * (taylorM x * (1 + taylorL x) ^ 3)) ^ (2 : ℕ) +
    16 * x ^ (-(3 : ℝ)) = x * taylorError x
  rw [mul_pow, Real.sq_sqrt hx₀.le, hneg, taylorError, columnError, hexp]
  field_simp

/-- The sum of the quadratic logarithm errors tends to zero. -/
theorem taylorLogError_mul_tendsto :
    Tendsto (fun x : ℝ ↦ x * (taylorM x + taylorError x) ^ 2) atTop (𝓝 0) := by
  have hs₀ : Tendsto (fun x : ℝ ↦ Real.sqrt x * taylorM x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ sqrt_mul_taylorSmall_tendsto
    · filter_upwards [eventually_large_taylorScale] with x hx
      exact mul_nonneg (Real.sqrt_nonneg _) (taylorM_nonneg hx.1)
    · filter_upwards [eventually_large_taylorScale] with x hx
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
      have hpow : 1 ≤ (1 + taylorL x) ^ (3 : ℕ) :=
        one_le_pow₀ (by linarith [taylorL_nonneg hx.1])
      exact le_mul_of_one_le_right (taylorM_nonneg hx.1) hpow
  have hs₁ : Tendsto (fun x : ℝ ↦ Real.sqrt x * taylorError x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ taylorError_mul_tendsto
    · exact Filter.Eventually.of_forall fun x ↦
        mul_nonneg (Real.sqrt_nonneg x) (taylorError_nonneg x)
    · filter_upwards [eventually_large_taylorScale] with x hx
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hx.1))
        (taylorError_nonneg x)
  have ht := (hs₀.add hs₁).pow 2
  simp only [add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ht
  apply ht.congr'
  filter_upwards [eventually_large_taylorScale] with x hx
  rw [← mul_add, mul_pow, Real.sq_sqrt (by linarith [hx.1])]


/-- The maximum-coordinate and integrated error bounds vanish. -/
theorem taylorM_add_error_tendsto :
    Tendsto (fun x : ℝ ↦ taylorM x + taylorError x) atTop (𝓝 0) := by
  have hM : Tendsto taylorM atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ taylorSmall_tendsto
    · filter_upwards [eventually_large_taylorScale] with x hx
      exact taylorM_nonneg hx.1
    · filter_upwards [eventually_large_taylorScale] with x hx
      have hpow : 1 ≤ (1 + taylorL x) ^ (3 : ℕ) :=
        one_le_pow₀ (by linarith [taylorL_nonneg hx.1])
      exact le_mul_of_one_le_right (taylorM_nonneg hx.1) hpow
  have hE : Tendsto taylorError atTop (𝓝 0) := by
    refine squeeze_zero' (.of_forall taylorError_nonneg) ?_ taylorError_mul_tendsto
    filter_upwards [eventually_large_taylorScale] with x hx
    exact le_mul_of_one_le_left (taylorError_nonneg x) hx.1
  simpa only [add_zero] using hM.add hE

/-- The total deterministic error in the product of columns tends to zero. -/
theorem taylorTotalError_tendsto :
    Tendsto (fun x : ℝ ↦ x * (taylorError x + 2 * (taylorM x + taylorError x) ^ 2))
      atTop (𝓝 0) := by
  have h := taylorError_mul_tendsto.add (taylorLogError_mul_tendsto.const_mul 2)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun x ↦ ?_
  ring

/-- The market size tends to infinity when indexed from size two. -/
theorem tendsto_rankSize : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)

/-- A logarithm is negligible compared with every positive power of the market size. -/
theorem tendsto_rankSize_log_div_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ ↦
      Real.log ((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) ^ δ)) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp tendsto_rankSize

/-- The normalized column cutoff and the coordinate bounds hold uniformly on interior windows. -/
theorem eventually_taylorWindow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ (q s : ℝ) (u : Vec (k + 2)),
      let N : ℝ := ((k + 2 : ℕ) : ℝ)
      0 < q → q ≤ 1 → N ^ δ / q ≤ s → s ≤ N ^ (1 - δ) →
      (∀ i, 0 ≤ u i) → (∀ i, u i ≤ taylorM N) →
      0 ≤ taylorM N ∧ 0 ≤ taylorL N ∧ taylorL N ≤ q * s ∧
        s • u ∈ cube (k + 2) ∧ ∀ i, u i * (q * s) ≤ 1 := by
  have hlim := tendsto_rankSize_log_div_rpow hδ
  have hLlim : Tendsto (fun k : ℕ ↦
      taylorL ((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) ^ δ)) atTop (𝓝 0) := by
    simpa only [taylorL, mul_div_assoc, mul_zero] using hlim.const_mul 8
  have hMlim : Tendsto (fun k : ℕ ↦
      4 * Real.log ((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) ^ δ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hlim.const_mul 4
  filter_upwards [hLlim.eventually (Iio_mem_nhds zero_lt_one),
    hMlim.eventually (Iio_mem_nhds zero_lt_one)] with k hkL hkM
  intro q s u N hq hq1 hslow hshigh hu huM
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (by omega : 1 ≤ k + 2)
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hpow : 0 < N ^ δ := Real.rpow_pos_of_pos hN _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hM : 0 ≤ taylorM N := div_nonneg (mul_nonneg (by norm_num) hlog) hN.le
  have hL : 0 ≤ taylorL N := mul_nonneg (by norm_num) hlog
  have hs : 0 ≤ s := (div_pos hpow hq).le.trans hslow
  have hLq : taylorL N ≤ q * s := by
    have h₁ : taylorL N / N ^ δ < 1 := hkL
    have h₂ := (div_lt_iff₀ hpow).mp h₁
    have h₃ := (div_le_iff₀ hq).mp hslow
    linarith [show q * s = s * q by ring]
  have hmul : N ^ (1 - δ) * taylorM N = 4 * Real.log N / N ^ δ := by
    rw [Real.rpow_sub hN, Real.rpow_one, taylorM]
    field_simp
  have hscale : s * taylorM N ≤ 1 := by
    calc
      _ ≤ N ^ (1 - δ) * taylorM N := mul_le_mul_of_nonneg_right hshigh hM
      _ = 4 * Real.log N / N ^ δ := hmul
      _ ≤ 1 := le_of_lt (show 4 * Real.log N / N ^ δ < 1 from hkM)
  have hcoord (i : Fin (k + 2)) : s * u i ≤ 1 :=
    (mul_le_mul_of_nonneg_left (huM i) hs).trans hscale
  refine ⟨hM, hL, hLq, ?_, ?_⟩
  · intro i _
    exact ⟨mul_nonneg hs (hu i), hcoord i⟩
  · intro i
    calc
      u i * (q * s) = q * (s * u i) := by ring
      _ ≤ s * u i := mul_le_of_le_one_left (mul_nonneg hs (hu i)) hq1
      _ ≤ 1 := hcoord i

/-- The deterministic product estimate's smallness conditions eventually hold. -/
theorem eventually_taylorSmall :
    ∀ᶠ k : ℕ in atTop,
      let N : ℝ := ((k + 2 : ℕ) : ℝ)
      taylorM N ≤ 1 / 2 ∧
        taylorM N * (1 + taylorL N) ^ 3 ≤ 1 / 4 ∧
        taylorM N + columnError (taylorM N) (taylorL N) ≤ 1 / 2 := by
  have hs := taylorSmall_tendsto.comp tendsto_rankSize
  have he := taylorM_add_error_tendsto.comp tendsto_rankSize
  filter_upwards [hs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk he
  have hE : taylorM (((k + 2 : ℕ) : ℝ)) +
      columnError (taylorM (((k + 2 : ℕ) : ℝ))) (taylorL (((k + 2 : ℕ) : ℝ))) < 1 / 2 := he
  exact ⟨(le_add_of_nonneg_right (columnError_nonneg _ _)).trans hE.le,
    (show _ < (1 / 4 : ℝ) from hk).le, hE.le⟩

/-- The logarithmic product error bound vanishes along the market-size sequence. -/
theorem tendsto_rankSize_taylorTotalError :
    Tendsto (fun k : ℕ ↦
      let N : ℝ := ((k + 2 : ℕ) : ℝ)
      let M := taylorM N
      let L := taylorL N
      N * (columnError M L + 2 * (M + columnError M L) ^ 2)) atTop (𝓝 0) :=
  taylorTotalError_tendsto.comp tendsto_rankSize

/-- A small error in the logarithm gives a small error in the positive radial weight. -/
theorem abs_sub_exp_neg_one_le_of_abs_log_add_one_le {w c : ℝ}
    (hw : 0 < w) (hc : c ≤ 1) (h : |Real.log w + 1| ≤ c) :
    |w - Real.exp (-1)| ≤ 2 * c := by
  let d := Real.log w + 1
  have hd : |d| ≤ c := h
  have hc₀ : 0 ≤ c := (abs_nonneg d).trans hd
  have hd2 : d ^ 2 ≤ c := by
    have hsq := pow_le_pow_left₀ (abs_nonneg d) hd 2
    rw [sq_abs] at hsq
    exact hsq.trans (by nlinarith [mul_nonneg hc₀ (sub_nonneg.mpr hc)])
  have hexp : |Real.exp d - 1| ≤ 2 * c := by
    calc
      |Real.exp d - 1| = |(Real.exp d - 1 - d) + d| := by congr 1; ring
      _ ≤ |Real.exp d - 1 - d| + |d| := abs_add_le _ _
      _ ≤ d ^ 2 + c := add_le_add (abs_exp_sub_one_sub_le (hd.trans hc)) hd
      _ ≤ 2 * c := by linarith
  have hw' : w = Real.exp (-1) * Real.exp d := by
    rw [← Real.exp_add, show -1 + d = Real.log w by dsimp [d]; ring, Real.exp_log hw]
  have hdif : w - Real.exp (-1) = Real.exp (-1) * (Real.exp d - 1) := by
    rw [hw']
    ring
  rw [hdif, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-1) * (2 * c) := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
    _ ≤ 2 * c := mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by norm_num))

end SupercriticalLogRank
