module

public import SupercriticalLogRank.Model

@[expose] public section

/-!
# Quantitative estimates for the column integrals

This file treats the one-dimensional product obtained by integrating out one worker's score.
The estimates are deterministic and apply uniformly on the interior logarithmic window.
-/

open scoped BigOperators
open Set MeasureTheory

namespace SupercriticalLogRank

theorem abs_log_one_sub_add_quad_le {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1 / 2) :
    |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * x ^ 3 := by
  let f (y : ℝ) := Real.log (1 - y) + y + y ^ 2 / 2
  let f' (y : ℝ) := -(y ^ 2) / (1 - y)
  have hd : ∀ y ∈ Icc 0 x, HasDerivWithinAt f (f' y) (Icc 0 x) y := by
    intro y hy
    have hy' : 1 - y ≠ 0 := by linarith [hy.2]
    have hsub := (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
    have hp := ((hasDerivAt_id y).pow 2).div_const (2 : ℝ)
    have h := ((hsub.log hy').add (hasDerivAt_id y)).add hp
    have h₁ : HasDerivAt f ((0 - 1) / (1 - y) + 1 + 2 * y / 2) y := by
      convert h using 1 <;> try rfl
      all_goals norm_num [Pi.add_apply, Pi.sub_apply]
    have h₂ : (0 - 1) / (1 - y) + 1 + 2 * y / 2 = f' y := by
      change _ = -(y ^ 2) / (1 - y)
      field_simp
      ring
    exact (h₂ ▸ h₁).hasDerivWithinAt
  have hb : ∀ y ∈ Icc 0 x, ‖f' y‖ ≤ 2 * x ^ 2 := by
    intro y hy
    have hy' : 0 < 1 - y := by linarith [hy.2]
    have hsq : y ^ 2 ≤ x ^ 2 := by gcongr <;> first | exact hy.1 | exact hy.2
    dsimp [f']
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg y), abs_of_pos hy']
    apply (div_le_iff₀ hy').2
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * y by linarith [hy.2])]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc 0 x) (left_mem_Icc.mpr hx₀) (right_mem_Icc.mpr hx₀)
  simpa [f, Real.norm_eq_abs, abs_of_nonneg hx₀, pow_succ, mul_assoc] using h

theorem abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  let f (y : ℝ) := Real.log (1 + y) - y
  let f' (y : ℝ) := -y / (1 + y)
  let s := Icc (-|x|) |x|
  have hd : ∀ y ∈ s, HasDerivWithinAt f (f' y) s y := by
    intro y hy
    have hy' : 1 + y ≠ 0 := by
      change -|x| ≤ y ∧ y ≤ |x| at hy
      linarith [hy.1]
    have hadd := (hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)
    have h := (hadd.log hy').sub (hasDerivAt_id y)
    have h₁ : HasDerivAt f ((0 + 1) / (1 + y) - 1) y := by
      convert h using 1 <;> try rfl
    have h₂ : (0 + 1) / (1 + y) - 1 = f' y := by
      change _ = -y / (1 + y)
      field_simp
      ring
    exact (h₂ ▸ h₁).hasDerivWithinAt
  have hb : ∀ y ∈ s, ‖f' y‖ ≤ 2 * |x| := by
    intro y hy
    change -|x| ≤ y ∧ y ≤ |x| at hy
    have hy' : 0 < 1 + y := by linarith [hy.1]
    have hy_abs : |y| ≤ |x| := abs_le.mpr hy
    dsimp [f']
    rw [abs_div, abs_neg, abs_of_pos hy']
    apply (div_le_iff₀ hy').2
    nlinarith [mul_nonneg (abs_nonneg x) (show 0 ≤ 1 + 2 * y by linarith [hy.1])]
  have hz : (0 : ℝ) ∈ s := ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
  have hxs : x ∈ s := ⟨neg_abs_le x, le_abs_self x⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (-|x|) |x|) hz hxs
  calc
    |Real.log (1 + x) - x| ≤ 2 * |x| * |x| := by simpa [f, Real.norm_eq_abs] using h
    _ = 2 * x ^ 2 := by rw [mul_assoc, ← pow_two, sq_abs]

theorem abs_exp_sub_one_sub_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x| ≤ x ^ 2 := by
  have h := Real.exp_bound (n := 2) hx (by decide)
  norm_num [Finset.sum_range_succ] at h
  rw [show Real.exp x - 1 - x = Real.exp x - (1 + x) by ring]
  exact h.trans (by nlinarith [sq_nonneg x])



/-- The integrated quadratic Taylor approximation to a column factor. -/
noncomputable def expQuadratic (a Q z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + a * z - Q * z ^ 2 / 2)

/-- Integrability of each integer moment of an exponential density. -/
theorem integrableOn_exp_neg_mul_pow_Ioi (k : ℕ) :
    IntegrableOn (fun z : ℝ ↦ Real.exp (-z) * z ^ k) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h

/-- The integer moments of an exponential density. -/
theorem integral_exp_neg_mul_pow_Ioi (k : ℕ) :
    (∫ z : ℝ in Ioi 0, Real.exp (-z) * z ^ k) = (k.factorial : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial]
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    (Real.Gamma_eq_integral (s := (k : ℝ) + 1) (by positivity)).symm

/-- The quadratic Taylor approximation is integrable above every nonnegative cutoff. -/
theorem integrableOn_expQuadratic {a Q L : ℝ} (hL : 0 ≤ L) :
    IntegrableOn (expQuadratic a Q) (Ioi L) := by
  have h₀ := integrableOn_exp_neg_mul_pow_Ioi 0
  have h₁ := (integrableOn_exp_neg_mul_pow_Ioi 1).const_mul a
  have h₂ := (integrableOn_exp_neg_mul_pow_Ioi 2).const_mul (Q / 2)
  have h := (h₀.add h₁).sub h₂
  have h' : IntegrableOn (expQuadratic a Q) (Ioi 0) := by
    refine h.congr <| Filter.Eventually.of_forall fun z ↦ ?_
    simp [expQuadratic]
    ring
  exact h'.mono_set (Ioi_subset_Ioi hL)

/-- The full integral of the quadratic Taylor approximation. -/
theorem integral_expQuadratic (a Q : ℝ) :
    (∫ z in Ioi 0, expQuadratic a Q z) = 1 + a - Q := by
  have h₀ := integrableOn_exp_neg_mul_pow_Ioi 0
  have h₁ := (integrableOn_exp_neg_mul_pow_Ioi 1).const_mul a
  have h₂ := (integrableOn_exp_neg_mul_pow_Ioi 2).const_mul (Q / 2)
  calc
    _ = ∫ z in Ioi 0, Real.exp (-z) * z ^ (0 : ℕ) +
        a * (Real.exp (-z) * z ^ (1 : ℕ)) - (Q / 2) * (Real.exp (-z) * z ^ (2 : ℕ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      simp [expQuadratic]
      ring
    _ = _ := by
      have h₀₁ : IntegrableOn (fun z : ℝ ↦ Real.exp (-z) * z ^ (0 : ℕ) +
          a * (Real.exp (-z) * z ^ (1 : ℕ))) (Ioi 0) := h₀.add h₁
      rw [integral_sub h₀₁ h₂, integral_add h₀ h₁]
      simp only [integral_const_mul, integral_exp_neg_mul_pow_Ioi]
      norm_num [Nat.factorial]

/-- The tail of the quadratic approximation is exponentially small. -/
theorem abs_integral_expQuadratic_tail_le {a Q L : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hQ₀ : 0 ≤ Q) (hQ₁ : Q ≤ 1) (hL : 0 ≤ L) :
    |∫ z in Ioi L, expQuadratic a Q z| ≤ 14 * Real.exp (-L / 2) := by
  have hdom (z : ℝ) (hz : 0 ≤ z) : ‖expQuadratic a Q z‖ ≤ 7 * Real.exp (-z / 2) := by
    rw [Real.norm_eq_abs, expQuadratic, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hz₁ : z / 2 ≤ Real.exp (z / 2) := by
      simpa using Real.pow_div_factorial_le_exp (x := z / 2) (by positivity) 1
    have hz₂ : (z / 2) ^ 2 / 2 ≤ Real.exp (z / 2) := by
      simpa [Nat.factorial] using
        Real.pow_div_factorial_le_exp (x := z / 2) (by positivity) 2
    have hz₀ := Real.one_le_exp (by positivity : 0 ≤ z / 2)
    have h : |1 + a * z - Q * z ^ 2 / 2| ≤ 7 * Real.exp (z / 2) := by
      have hzQ : 0 ≤ Q * z ^ 2 / 2 := by positivity
      have hza : 0 ≤ 1 + a * z := by positivity
      have htriangle := abs_sub_le (1 + a * z) 0 (Q * z ^ 2 / 2)
      simp only [sub_zero, zero_sub, abs_neg] at htriangle
      refine htriangle.trans ?_
      rw [abs_of_nonneg hzQ, abs_of_nonneg hza]
      have ha : a * z ≤ z := mul_le_of_le_one_left hz ha₁
      have hQ : Q * z ^ 2 ≤ z ^ 2 := mul_le_of_le_one_left (sq_nonneg z) hQ₁
      linarith
    calc
      _ ≤ Real.exp (-z) * (7 * Real.exp (z / 2)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
  have hi : IntegrableOn (fun z : ℝ ↦ 7 * Real.exp (-z / 2)) (Ioi L) := by
    change Integrable _ _
    simpa only [show ∀ z : ℝ, -z / 2 = (-(1 / 2 : ℝ)) * z by intro z; ring] using
      (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) L).const_mul 7
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z in Ioi L, ‖expQuadratic a Q z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in Ioi L, 7 * Real.exp (-z / 2) := by
      exact setIntegral_mono_on (integrableOn_expQuadratic hL).norm hi measurableSet_Ioi
        (fun z hz ↦ hdom z (hL.trans (mem_Ioi.mp hz).le))
    _ = _ := by
      simp_rw [show ∀ z : ℝ, -z / 2 = (-(1 / 2 : ℝ)) * z by intro z; ring]
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
      ring


/-- Integrating a pointwise Taylor approximation and controlling its exponential tails. -/
theorem abs_intervalIntegral_sub_expQuadratic_le
    {P : ℝ → ℝ} {a Q L B E : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hQ₀ : 0 ≤ Q) (hQ₁ : Q ≤ 1)
    (hL : 0 ≤ L) (hLB : L ≤ B) (hE : 0 ≤ E)
    (hP : Continuous P)
    (happrox : ∀ z ∈ Icc 0 L, |P z - expQuadratic a Q z| ≤ Real.exp (-z) * E)
    (htail : ∀ z ∈ Icc L B, |P z| ≤ Real.exp (-z / 2)) :
    |(∫ z in 0..B, P z) - (1 + a - Q)| ≤ E + 16 * Real.exp (-L / 2) := by
  have hQc : Continuous (expQuadratic a Q) := by unfold expQuadratic; fun_prop
  have hP₀ : IntervalIntegrable P volume 0 L := hP.intervalIntegrable _ _
  have hP₁ : IntervalIntegrable P volume L B := hP.intervalIntegrable _ _
  have hQ₂ : IntervalIntegrable (expQuadratic a Q) volume 0 L :=
    hQc.intervalIntegrable _ _
  have hexp_c : Continuous (fun z : ℝ ↦ Real.exp (-z)) := by fun_prop
  have hexp_half_c : Continuous (fun z : ℝ ↦ Real.exp (-z / 2)) := by fun_prop
  have hexp₀ : (∫ z : ℝ in 0..L, Real.exp (-z)) ≤ 1 := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_neg_Ioi 0) hL,
      integral_exp_neg_Ioi_zero, integral_exp_neg_Ioi]
    linarith [Real.exp_pos (-L)]
  have herror :
      |(∫ z in 0..L, P z) - ∫ z in 0..L, expQuadratic a Q z| ≤ E := by
    rw [← intervalIntegral.integral_sub hP₀ hQ₂]
    calc
      _ ≤ ∫ z in 0..L, |P z - expQuadratic a Q z| :=
        intervalIntegral.abs_integral_le_integral_abs hL
      _ ≤ ∫ z : ℝ in 0..L, Real.exp (-z) * E :=
        intervalIntegral.integral_mono_on hL
          ((hP.sub hQc).abs.intervalIntegrable _ _) ((hexp_c.mul continuous_const).intervalIntegrable _ _)
          happrox
      _ ≤ E := by
        rw [intervalIntegral.integral_mul_const]
        nlinarith only [mul_le_mul_of_nonneg_right hexp₀ hE]
  have hexp_half (c : ℝ) : IntegrableOn (fun z : ℝ ↦ Real.exp (-z / 2)) (Ioi c) := by
    simpa only [show ∀ z : ℝ, -z / 2 = (-(1 / 2 : ℝ)) * z by intro z; ring] using
      integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) c
  have hexp_half_eq (c : ℝ) :
      (∫ z : ℝ in Ioi c, Real.exp (-z / 2)) = 2 * Real.exp (-c / 2) := by
    simp_rw [show ∀ z : ℝ, -z / 2 = (-(1 / 2 : ℝ)) * z by intro z; ring]
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
    ring
  have hPtail : |∫ z in L..B, P z| ≤ 2 * Real.exp (-L / 2) := calc
    _ ≤ ∫ z in L..B, |P z| := intervalIntegral.abs_integral_le_integral_abs hLB
    _ ≤ ∫ z : ℝ in L..B, Real.exp (-z / 2) :=
      intervalIntegral.integral_mono_on hLB (hP.abs.intervalIntegrable _ _)
        (hexp_half_c.intervalIntegrable _ _) htail
    _ ≤ _ := by
      rw [← intervalIntegral.integral_Ioi_sub_Ioi (hexp_half L) hLB, hexp_half_eq, hexp_half_eq]
      linarith [Real.exp_pos (-B / 2)]
  have hQtail := abs_integral_expQuadratic_tail_le ha₀ ha₁ hQ₀ hQ₁ hL
  have hQsplit := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_expQuadratic (a := a) (Q := Q) (L := 0) le_rfl)
    (integrableOn_expQuadratic (a := a) (Q := Q) hL)
  rw [integral_expQuadratic] at hQsplit
  rw [← intervalIntegral.integral_add_adjacent_intervals hP₀ hP₁, ← hQsplit]
  let A := ∫ z in 0..L, P z
  let C := ∫ z in L..B, P z
  let U := ∫ z in 0..L, expQuadratic a Q z
  let V := ∫ z in Ioi L, expQuadratic a Q z
  change |A + C - (U + V)| ≤ _
  rw [show A + C - (U + V) = (A - U + C) - V by ring]
  calc
    _ ≤ |A - U + C| + |V| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (A - U + C) 0 V
    _ ≤ |A - U| + |C| + |V| := by linarith only [abs_add_le (A - U) C]
    _ ≤ _ := by
      change |A - U| ≤ E at herror
      change |C| ≤ _ at hPtail
      change |V| ≤ _ at hQtail
      linarith only [herror, hPtail, hQtail]


section Column

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integrand for one normalized column. -/
noncomputable def columnProduct (u : ι → ℝ) (j : ι) (z : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, (1 - u i * z)

/-- The column product is nonnegative below the first zero of any factor. -/
theorem columnProduct_nonneg {u : ι → ℝ} {j : ι} {z : ℝ}
    (h : ∀ i, u i * z ≤ 1) : 0 ≤ columnProduct u j z := by
  exact Finset.prod_nonneg (fun i _ ↦ sub_nonneg.mpr (h i))

/-- Comparison with the exponential obtained by summing the column's coefficients. -/
theorem columnProduct_le_exp {u : ι → ℝ} {j : ι} {z : ℝ}
    (hsum : ∑ i, u i = 1) (h : ∀ i, u i * z ≤ 1) :
    columnProduct u j z ≤ Real.exp (-(1 - u j) * z) := by
  have hsum' : ∑ i ∈ Finset.univ.erase j, u i = 1 - u j := by
    have := Finset.sum_erase_add Finset.univ u (Finset.mem_univ j)
    linarith
  calc
    columnProduct u j z ≤ ∏ i ∈ Finset.univ.erase j, Real.exp (-(u i * z)) := by
      exact Finset.prod_le_prod₀ (fun i _ ↦ sub_nonneg.mpr (h i))
        (fun i _ ↦ by simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(u i * z)))
    _ = Real.exp (-(1 - u j) * z) := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_neg_distrib, ← Finset.sum_mul, hsum']
      ring

/-- Each column polynomial is continuous on the real line. -/
theorem continuous_columnProduct (u : ι → ℝ) (j : ι) :
    Continuous (columnProduct u j) := by
  unfold columnProduct
  fun_prop

/-- Logarithmic expansion of one column, including the omitted diagonal factor. -/
theorem abs_log_columnProduct_sub_le {u : ι → ℝ} {j : ι} {z M : ℝ}
    (hu : ∀ i, 0 ≤ u i) (huM : ∀ i, u i ≤ M)
    (hsum : ∑ i, u i = 1) (hz : 0 ≤ z) (hsmall : M * z ≤ 1 / 2) :
    |Real.log (columnProduct u j z) -
      (-z + u j * z - (∑ i, u i ^ 2) * z ^ 2 / 2)| ≤
      M ^ 2 * (z ^ 2 / 2 + 2 * z ^ 3) := by
  have hhalf (i : ι) : u i * z ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (huM i) hz).trans hsmall
  have hlog : Real.log (columnProduct u j z) =
      ∑ i ∈ Finset.univ.erase j, Real.log (1 - u i * z) := by
    rw [columnProduct, Real.log_prod]
    exact fun i _ ↦ ne_of_gt (by linarith [hhalf i])
  have hlin : ∑ i ∈ Finset.univ.erase j, u i = 1 - u j := by
    have := Finset.sum_erase_add Finset.univ u (Finset.mem_univ j)
    linarith
  have hsq : ∑ i ∈ Finset.univ.erase j, u i ^ 2 = (∑ i, u i ^ 2) - u j ^ 2 := by
    have := Finset.sum_erase_add Finset.univ (fun i ↦ u i ^ 2) (Finset.mem_univ j)
    linarith
  let f (i : ι) := Real.log (1 - u i * z) + u i * z + (u i * z) ^ 2 / 2
  have hf : |∑ i ∈ Finset.univ.erase j, f i| ≤ 2 * M ^ 2 * z ^ 3 := by
    calc
      |∑ i ∈ Finset.univ.erase j, f i| ≤ ∑ i ∈ Finset.univ.erase j, |f i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.erase j, (2 * M ^ 2 * z ^ 3) * u i := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |f i| ≤ 2 * (u i * z) ^ 3 := abs_log_one_sub_add_quad_le (mul_nonneg (hu i) hz) (hhalf i)
          _ = (2 * u i ^ 2 * z ^ 3) * u i := by ring
          _ ≤ (2 * M ^ 2 * z ^ 3) * u i := by
            gcongr <;> first | exact hu i | exact huM i
      _ = (2 * M ^ 2 * z ^ 3) * (1 - u j) := by rw [← Finset.mul_sum, hlin]
      _ ≤ 2 * M ^ 2 * z ^ 3 := by
        have hcoef : 0 ≤ 2 * M ^ 2 * z ^ 3 := by positivity
        nlinarith [mul_nonneg hcoef (hu j)]
  have hdecomp : Real.log (columnProduct u j z) -
      (-z + u j * z - (∑ i, u i ^ 2) * z ^ 2 / 2) =
        (∑ i ∈ Finset.univ.erase j, f i) + u j ^ 2 * z ^ 2 / 2 := by
    rw [hlog]
    simp only [f, Finset.sum_add_distrib, mul_pow, ← Finset.sum_div, ← Finset.sum_mul, hlin, hsq]
    ring
  rw [hdecomp]
  calc
    |_| ≤ |∑ i ∈ Finset.univ.erase j, f i| + |u j ^ 2 * z ^ 2 / 2| := abs_add_le _ _
    _ ≤ 2 * M ^ 2 * z ^ 3 + M ^ 2 * z ^ 2 / 2 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ u j ^ 2 * z ^ 2 / 2)]
      exact add_le_add hf (by gcongr <;> first | exact hu j | exact huM j)
    _ = M ^ 2 * (z ^ 2 / 2 + 2 * z ^ 3) := by ring

/-- A uniform pointwise approximation on a bounded initial integration interval. -/
theorem abs_columnProduct_sub_exp_quad_le {u : ι → ℝ} {j : ι} {z L M : ℝ}
    (hu : ∀ i, 0 ≤ u i) (huM : ∀ i, u i ≤ M) (hM : 0 ≤ M)
    (hsum : ∑ i, u i = 1) (hz : 0 ≤ z) (hzL : z ≤ L)
    (hsmall : M * (1 + L) ^ 3 ≤ 1 / 4) :
    |columnProduct u j z - Real.exp (-z) * (1 + u j * z - (∑ i, u i ^ 2) * z ^ 2 / 2)| ≤
      Real.exp (-z) * (7 * (M * (1 + L) ^ 3) ^ 2) := by
  let Q := ∑ i, u i ^ 2
  let C := (1 + L) ^ 3
  let T := M * C
  have hL : 0 ≤ L := hz.trans hzL
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hQM : Q ≤ M := by
    calc
      Q ≤ ∑ i, M * u i := by
        apply Finset.sum_le_sum
        intro i _
        simpa [pow_two] using mul_le_mul_of_nonneg_right (huM i) (hu i)
      _ = M := by rw [← Finset.mul_sum, hsum, mul_one]
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg L, pow_nonneg hL 3]
  have hCL : z + z ^ 2 / 2 ≤ C := by
    have h2 : z ^ 2 ≤ L ^ 2 := by gcongr
    dsimp [C]
    nlinarith [sq_nonneg L, pow_nonneg hL 3]
  have hC' : z ^ 2 / 2 + 2 * z ^ 3 ≤ 3 * C ^ 2 := by
    have h2 : z ^ 2 ≤ L ^ 2 := by gcongr
    have h3 : z ^ 3 ≤ L ^ 3 := by gcongr
    have hC2 : C ≤ C ^ 2 := by nlinarith
    have : z ^ 2 / 2 + 2 * z ^ 3 ≤ 3 * C := by
      dsimp [C]
      nlinarith [sq_nonneg L, pow_nonneg hL 3]
    linarith
  have hT : 0 ≤ T := mul_nonneg hM (by linarith)
  have hTsmall : T ≤ 1 / 4 := hsmall
  have hMz : M * z ≤ 1 / 2 := by
    have hzC : z ≤ C := by nlinarith [sq_nonneg z]
    have hMzT : M * z ≤ T := mul_le_mul_of_nonneg_left hzC hM
    linarith
  have hP : 0 < columnProduct u j z := by
    exact Finset.prod_pos (fun i _ ↦ by
      have h := (mul_le_mul_of_nonneg_right (huM i) hz).trans hMz
      linarith)
  let b := u j * z - Q * z ^ 2 / 2
  let d := Real.log (columnProduct u j z) + z
  have hb : |b| ≤ T := by
    calc
      |b| ≤ u j * z + Q * z ^ 2 / 2 := by
        apply abs_le.mpr
        dsimp [b]
        constructor <;> linarith [mul_nonneg (hu j) hz, mul_nonneg hQ (sq_nonneg z)]
      _ ≤ M * z + M * z ^ 2 / 2 := by gcongr; exact huM j
      _ = M * (z + z ^ 2 / 2) := by ring
      _ ≤ T := mul_le_mul_of_nonneg_left hCL hM
  have hdb : |d - b| ≤ 3 * T ^ 2 := by
    have hlog := abs_log_columnProduct_sub_le (j := j) hu huM hsum hz hMz
    have he : d - b = Real.log (columnProduct u j z) - (-z + u j * z - Q * z ^ 2 / 2) := by
      dsimp [d, b]
      ring
    rw [he]
    calc
      _ ≤ M ^ 2 * (z ^ 2 / 2 + 2 * z ^ 3) := hlog
      _ ≤ M ^ 2 * (3 * C ^ 2) := mul_le_mul_of_nonneg_left hC' (sq_nonneg M)
      _ = 3 * T ^ 2 := by dsimp [T]; ring
  have hd : |d| ≤ 2 * T := by
    have he : d = (d - b) + b := by ring
    calc
      |d| = |(d - b) + b| := by rw [← he]
      _ ≤ |d - b| + |b| := abs_add_le _ _
      _ ≤ 3 * T ^ 2 + T := add_le_add hdb hb
      _ ≤ 2 * T := by nlinarith [mul_nonneg hT (show 0 ≤ 1 / 4 - T by linarith)]
  have hexp : |Real.exp d - 1 - b| ≤ 7 * T ^ 2 := by
    have hd1 : |d| ≤ 1 := by linarith
    have he : Real.exp d - 1 - b = (Real.exp d - 1 - d) + (d - b) := by ring
    rw [he]
    calc
      _ ≤ |Real.exp d - 1 - d| + |d - b| := abs_add_le _ _
      _ ≤ d ^ 2 + 3 * T ^ 2 := add_le_add (abs_exp_sub_one_sub_le hd1) hdb
      _ ≤ 7 * T ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg d) hd 2
        rw [sq_abs] at h
        nlinarith
  have heq : columnProduct u j z = Real.exp (-z) * Real.exp d := by
    rw [← Real.exp_add]
    rw [show -z + d = Real.log (columnProduct u j z) by dsimp [d]; ring, Real.exp_log hP]
  rw [heq, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rw [show 1 + u j * z - (∑ i, u i ^ 2) * z ^ 2 / 2 = 1 + b by dsimp [b, Q]; ring,
    show Real.exp d - (1 + b) = Real.exp d - 1 - b by ring]
  exact hexp

end Column

/-- A bound for the error in a column integral truncated at $L$. -/
noncomputable def columnError (M L : ℝ) : ℝ :=
  7 * (M * (1 + L) ^ 3) ^ 2 + 16 * Real.exp (-L / 2)

/-- The deterministic column error is nonnegative. -/
theorem columnError_nonneg (M L : ℝ) : 0 ≤ columnError M L := by
  unfold columnError
  positivity

/-- Integrated second-order approximation for a normalized worker column. -/
theorem abs_columnIntegral_sub_le {n : ℕ} {u : Vec n} {j : Fin n} {q s M L : ℝ}
    (hu : ∀ i, 0 ≤ u i) (huM : ∀ i, u i ≤ M) (hM : 0 ≤ M) (hMhalf : M ≤ 1 / 2)
    (hsum : ∑ i, u i = 1) (hL : 0 ≤ L) (hLB : L ≤ q * s)
    (hsmall : M * (1 + L) ^ 3 ≤ 1 / 4) (hcap : ∀ i, u i * (q * s) ≤ 1) :
    |columnIntegral q s u j - (1 + u j - ∑ i, u i ^ 2)| ≤ columnError M L := by
  let Q := ∑ i, u i ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hQM : Q ≤ M := by
    calc
      Q ≤ ∑ i, M * u i := by
        apply Finset.sum_le_sum
        intro i _
        simpa [pow_two] using mul_le_mul_of_nonneg_right (huM i) (hu i)
      _ = M := by rw [← Finset.mul_sum, hsum, mul_one]
  change |(∫ z in 0..(q * s), columnProduct u j z) - (1 + u j - Q)| ≤
    7 * (M * (1 + L) ^ 3) ^ 2 + 16 * Real.exp (-L / 2)
  refine abs_intervalIntegral_sub_expQuadratic_le (hu j) (by linarith [huM j])
    hQ (by linarith) hL hLB (by positivity) (continuous_columnProduct u j) ?_ ?_
  · intro z hz
    exact abs_columnProduct_sub_exp_quad_le hu huM hM hsum hz.1 hz.2 hsmall
  · intro z hz
    have hz₀ : 0 ≤ z := hL.trans hz.1
    have hzcap (i : Fin n) : u i * z ≤ 1 :=
      (mul_le_mul_of_nonneg_left hz.2 (hu i)).trans (hcap i)
    rw [abs_of_nonneg (columnProduct_nonneg hzcap)]
    apply (columnProduct_le_exp hsum hzcap).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hz₀ (show 0 ≤ 1 / 2 - u j by linarith [huM j])]

/-- A uniform bound on all column errors implies a bound on the logarithm of their product. -/
theorem prod_pos_and_abs_log_prod_sub_le {ι : Type*} [Fintype ι] (u J : ι → ℝ)
    {M e Q : ℝ} (huSum : ∑ j, u j = 1) (hu₀ : ∀ j, 0 ≤ u j)
    (huM : ∀ j, u j ≤ M) (hQ : Q = ∑ j, (u j)^2) (he₀ : 0 ≤ e)
    (hMe : M + e ≤ 1 / 2) (hJ : ∀ j, |J j - (1 + u j - Q)| ≤ e) :
    0 < ∏ j, J j ∧
      |Real.log (∏ j, J j) - (1 - (Fintype.card ι : ℝ) * Q)| ≤
        (Fintype.card ι : ℝ) * (e + 2 * (M + e)^2) := by
  have hQ₀ : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hQM : Q ≤ M := by
    calc
      Q = ∑ j, (u j)^2 := hQ
      _ ≤ ∑ j, M * u j := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (huM j) (hu₀ j)
      _ = M := by rw [← Finset.mul_sum, huSum, mul_one]
  have hMe₀ : 0 ≤ M + e := add_nonneg (hQ₀.trans hQM) he₀
  have huQ (j : ι) : |u j - Q| ≤ M := abs_le.mpr ⟨by linarith [hu₀ j], by linarith [huM j]⟩
  have hdist (j : ι) : |J j - 1| ≤ M + e := by
    calc
      |J j - 1| = |(J j - (1 + u j - Q)) + (u j - Q)| := by
        congr 1
        ring
      _ ≤ |J j - (1 + u j - Q)| + |u j - Q| := abs_add_le _ _
      _ ≤ M + e := by linarith [hJ j, huQ j]
  have hpos (j : ι) : 0 < J j := by linarith [(abs_le.mp (hdist j)).1]
  refine ⟨Finset.prod_pos fun j _ ↦ hpos j, ?_⟩
  have hsum : ∑ j, (u j - Q) = 1 - (Fintype.card ι : ℝ) * Q := by
    rw [Finset.sum_sub_distrib, huSum]
    simp [nsmul_eq_mul]
  rw [Real.log_prod (fun j _ ↦ (hpos j).ne'), ← hsum, ← Finset.sum_sub_distrib]
  calc
    |∑ j, (Real.log (J j) - (u j - Q))| ≤ ∑ j, |Real.log (J j) - (u j - Q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, (e + 2 * (M + e)^2) := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have hlog := abs_log_one_add_sub_le ((hdist j).trans hMe)
      rw [show 1 + (J j - 1) = J j by ring] at hlog
      have hsq : (J j - 1)^2 ≤ (M + e)^2 := by
        apply sq_le_sq.mpr
        simpa only [abs_of_nonneg hMe₀] using hdist j
      calc
        |Real.log (J j) - (u j - Q)| =
            |(Real.log (J j) - (J j - 1)) + (J j - (1 + u j - Q))| := by
              congr 1
              ring
        _ ≤ |Real.log (J j) - (J j - 1)| + |J j - (1 + u j - Q)| := abs_add_le _ _
        _ ≤ e + 2 * (M + e)^2 := by linarith [hJ j]
    _ = (Fintype.card ι : ℝ) * (e + 2 * (M + e)^2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Reciprocal factors for a simplex vector with each coordinate at most one half. -/
theorem prod_inv_one_sub_le_exp_two {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (huSum : ∑ j, u j = 1) (hu₀ : ∀ j, 0 ≤ u j) (hu : ∀ j, u j ≤ 1 / 2) :
    (∏ j, (1 - u j)⁻¹) ≤ Real.exp 2 := by
  have hpos (j : ι) : 0 < 1 - u j := by linarith [hu j]
  calc
    (∏ j, (1 - u j)⁻¹) ≤ ∏ j, Real.exp (2 * u j) := by
      refine Finset.prod_le_prod₀ (fun j _ ↦ inv_nonneg.mpr (hpos j).le) fun j _ ↦ ?_
      have h : (1 - u j)⁻¹ ≤ 1 + 2 * u j := by
        rw [inv_eq_one_div, div_le_iff₀ (hpos j)]
        nlinarith [mul_nonneg (hu₀ j) (show 0 ≤ 1 - 2 * u j by linarith [hu j])]
      exact h.trans (by simpa [add_comm] using Real.add_one_le_exp (2 * u j))
    _ = Real.exp 2 := by rw [← Real.exp_sum, ← Finset.mul_sum, huSum, mul_one]

/-- Positive radial weight and its uniform second-order logarithmic approximation. -/
theorem abs_log_radialWeight_sub_le {n : ℕ} {u : Vec n} {q s M L : ℝ}
    (hu : ∀ i, 0 ≤ u i) (huM : ∀ i, u i ≤ M) (hM : 0 ≤ M) (hMhalf : M ≤ 1 / 2)
    (hsum : ∑ i, u i = 1) (hL : 0 ≤ L) (hLB : L ≤ q * s)
    (hsmall : M * (1 + L) ^ 3 ≤ 1 / 4) (hcap : ∀ i, u i * (q * s) ≤ 1)
    (hME : M + columnError M L ≤ 1 / 2) (hcube : s • u ∈ cube n) :
    0 < radialWeight n q s u ∧
      |Real.log (radialWeight n q s u) - (1 - (n : ℝ) * ∑ i, u i ^ 2)| ≤
        (n : ℝ) * (columnError M L + 2 * (M + columnError M L) ^ 2) := by
  rw [radialWeight, ite_eq_left hcube]
  simpa only [Fintype.card_fin] using
    prod_pos_and_abs_log_prod_sub_le u (columnIntegral q s u) hsum hu huM rfl
      (columnError_nonneg M L) hME
      (fun _ ↦ abs_columnIntegral_sub_le hu huM hM hMhalf hsum hL hLB hsmall hcap)

end SupercriticalLogRank
