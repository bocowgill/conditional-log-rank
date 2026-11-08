module

public import SupercriticalLogRank.MarketBasics

@[expose] public section

/-! Positivity and cutoff identities for the logarithmic rank variables. -/

namespace SupercriticalLogRank

open Set

/-- Each firm's own partner contributes one to the rank count. -/
theorem card_le_firmRankSum {n : ℕ} (p : Profile n) : n ≤ firmRankSum p := by
  classical
  calc
    n = ∑ _i : Fin n, (1 : ℕ) := by simp
    _ ≤ firmRankSum p := by
      unfold firmRankSum
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have h := Finset.single_le_sum
        (f := fun j : Fin n ↦ if p (false, i, i) ≤ p (false, i, j) then (1 : ℕ) else 0)
        (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      simpa using h

private theorem diagonalScoreSum_pos {n : ℕ} (hn : 0 < n) (p : Profile n) (b : Bool) :
    0 < scoreSum (fun i ↦ Real.exp (-p (b, i, i))) := by
  let i : Fin n := ⟨0, hn⟩
  refine lt_of_lt_of_le (Real.exp_pos (-p (b, i, i))) ?_
  exact Finset.single_le_sum (fun j _ ↦ Real.exp_nonneg (-p (b, j, j))) (Finset.mem_univ i)

theorem diagonalFirmScoreSum_pos {n : ℕ} (hn : 0 < n) (p : Profile n) :
    0 < scoreSum (diagonalFirmScores p) :=
  diagonalScoreSum_pos hn p false

theorem diagonalWorkerScoreSum_pos {n : ℕ} (hn : 0 < n) (p : Profile n) :
    0 < scoreSum (diagonalWorkerScores p) :=
  diagonalScoreSum_pos hn p true

/-- The power cutoff for the total rank is the cutoff at the same parameter
for its logarithmic normalization. -/
theorem logRank_le_iff_mem_rankCutoffEvent {n : ℕ} (hn : 2 ≤ n) (p : Profile n) (t : ℝ) :
    Real.log ((firmRankSum p : ℝ) / n) / Real.log n ≤ t ↔ p ∈ rankCutoffEvent n t := by
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hr : 0 < (firmRankSum p : ℝ) := by
    exact lt_of_lt_of_le hn₀ (by exact_mod_cast card_le_firmRankSum p)
  change Real.log ((firmRankSum p : ℝ) / n) / Real.log n ≤ t ↔
    (firmRankSum p : ℝ) ≤ (n : ℝ) ^ (1 + t)
  calc
    _ ↔ Real.log (firmRankSum p : ℝ) ≤ (1 + t) * Real.log n := by
      rw [div_le_iff₀ (Real.log_pos hn₁), Real.log_div hr.ne' hn₀.ne']
      constructor <;> intro h <;> linarith
    _ ↔ _ := by
      rw [← Real.log_rpow hn₀ (1 + t)]
      exact Real.log_le_log_iff hr (Real.rpow_pos_of_pos hn₀ _)

end SupercriticalLogRank
