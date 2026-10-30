module

public import Freezing2.Discrete.Estimates
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The critical population hypothesis

Theorem `thm:critique` assumes `max_{1 ≤ k ≤ n} S^n_k = O(√n)`. Since each
positive row is a finite signed walk, this yields one constant `M` bounding
every positive row at every index `0 ≤ i ≤ n`, as chosen at the start of the
proofs of `OneStepTightness` and `tightness time estimate`.
-/

@[expose] public section

open Filter Asymptotics

namespace Freezing2

/-- The source maximum `max_{1 ≤ k ≤ n} S_k`. Negative values are clipped, which
is harmless on surviving rows; the empty maximum at `n = 0` is zero. -/
def rowMaxPopulation (x : ℕ → ℤ) (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (fun k ↦ (activeCount x k).toNat)

theorem activeCount_le_rowMaxPopulation (x : ℕ → ℤ) {n k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n) : activeCount x k ≤ rowMaxPopulation x n := by
  have h : (activeCount x k).toNat ≤ rowMaxPopulation x n :=
    Finset.le_sup (f := fun k ↦ (activeCount x k).toNat) (Finset.mem_Icc.mpr ⟨hk, hkn⟩)
  omega

/-- The source `O(√n)` population hypothesis gives one bound for all positive rows. -/
theorem exists_uniform_population_bound {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n))
    (hO : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ n : ℕ, 0 < n → ∀ i ≤ n,
      (activeCount (x n) i : ℝ) ≤ M * Real.sqrt n := by
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  refine ⟨max 1 (max c (N + 1)), le_max_left _ _, ?_⟩
  intro n hn i hi
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hM1 : (1 : ℝ) ≤ max 1 (max c (N + 1)) := le_max_left _ _
  have hMc : c ≤ max 1 (max c (N + 1)) := (le_max_left _ _).trans (le_max_right _ _)
  have hMN : (N : ℝ) + 1 ≤ max 1 (max c (N + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp only [activeCount_zero, Int.cast_one]
    nlinarith
  by_cases hnN : N ≤ n
  · have hb := hN n hnN
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Nat.abs_cast] at hb
    have hr : (activeCount (x n) i : ℝ) ≤ rowMaxPopulation (x n) n := by
      exact_mod_cast activeCount_le_rowMaxPopulation (x n) hi0 hi
    exact hr.trans (hb.trans (mul_le_mul_of_nonneg_right hMc (Real.sqrt_nonneg _)))
  · have ha := activeCount_le_time_add_one (x n) (hx n hn) i
    have haR : (activeCount (x n) i : ℝ) ≤ (N : ℝ) + 1 := by
      have : activeCount (x n) i ≤ (N : ℤ) + 1 := by omega
      exact_mod_cast this
    nlinarith

end Freezing2
