module

public import Freezing2.Probability.TrackedClusterExpectation

/-!
# Population-bounded blocks of the actual reverse process

The exact signed-walk count turns the proved expectation recurrence into
the source U35 block estimate. The start and end phases are nonnegative by
an explicit horizon bound; absorption at one component is already handled.
This does not assume or prove the oldest-singleton comparison of U34.
-/

@[expose] public section

open scoped BigOperators

namespace Freezing2.TrackedClusters

open Freezing1

/-- Twice the number of up steps is the elapsed length plus the population
change, including both actual phase endpoints. -/
theorem twice_attachmentSteps_card (x : SignSequence) (n k₀ m : ℕ)
    (hblock : k₀ + m ≤ n) :
    2 * ((attachmentSteps x n k₀ m).card : ℝ) =
      m + (activeCount x (n - k₀) : ℝ) - activeCount x (n - (k₀ + m)) := by
  induction m with
  | zero => simp [attachmentSteps]
  | succ m ih =>
      have hm : k₀ + m ≤ n := by omega
      have hcount : ((attachmentSteps x n k₀ (m + 1)).card : ℝ) =
          (attachmentSteps x n k₀ m).card + if x (n - (k₀ + m)) then 1 else 0 := by
        rw [← sum_attachment_indicators, Finset.sum_range_succ, sum_attachment_indicators]
      have ht : n - (k₀ + (m + 1)) + 1 = n - (k₀ + m) := by omega
      have hwalk := activeCount_succ x (n - (k₀ + (m + 1)))
      rw [ht] at hwalk
      have hi := ih hm
      rw [hcount]
      cases hs : x (n - (k₀ + m))
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
        have hw : (activeCount x (n - (k₀ + m)) : ℝ) =
            activeCount x (n - (k₀ + (m + 1))) - 1 := by exact_mod_cast hwalk
        push_cast
        linarith
      · simp only [hs, ↓reduceIte] at hwalk ⊢
        have hw : (activeCount x (n - (k₀ + m)) : ℝ) =
            activeCount x (n - (k₀ + (m + 1))) + 1 := by exact_mod_cast hwalk
        push_cast
        linarith

/-- Under a uniform population bound, a block longer than that bound has
a positive number of attachment steps and a quantitative lower bound. -/
theorem attachmentSteps_card_lower_bound {x : SignSequence} {n k₀ m : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hblock : k₀ + m ≤ n)
    {M : ℝ} (hM : ∀ t ≤ n, (activeCount x t : ℝ) ≤ M) :
    ((m : ℝ) - M) / 2 ≤ (attachmentSteps x n k₀ m).card := by
  have he := twice_attachmentSteps_card x n k₀ m hblock
  have hstart : (0 : ℝ) ≤ activeCount x (n - k₀) := by
    exact_mod_cast activeCount_nonneg_of_le_extinctionTime
      (le_trans (by exact_mod_cast Nat.sub_le n k₀) hn)
  have hend := hM (n - (k₀ + m)) (Nat.sub_le _ _)
  linarith

/-- The actual count at the block endpoint is at most
`1 + 2 M² / (m - M)`. The source's extra `-1` is unnecessary with the
exact endpoint count. All marked vertices must be present at block start. -/
theorem expectedCount_block_bound_of_population_bound {x : SignSequence}
    {n k₀ m : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x) (hblock : k₀ + m ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, n - k₀ ≤ birthTime n v)
    {M : ℝ} (hM0 : 0 < M) (hM : ∀ t ≤ n, (activeCount x t : ℝ) ≤ M)
    (hm : M < m) :
    expectedCount x n (k₀ + m) A ≤ 1 + 2 * M ^ 2 / ((m : ℝ) - M) := by
  have hcount := attachmentSteps_card_lower_bound hn hblock hM
  have hden : 0 < ((m : ℝ) - M) / 2 := by linarith
  have hpos : 0 < (attachmentSteps x n k₀ m).card := by
    exact_mod_cast hden.trans_le hcount
  have hp : ∀ j < m, x (n - (k₀ + j)) = true →
      (activeCount x (n - (k₀ + j)) : ℝ) ^ 2 ≤ M ^ 2 := by
    intro j _ _
    have h0 : (0 : ℝ) ≤ activeCount x (n - (k₀ + j)) := by
      exact_mod_cast activeCount_nonneg_of_le_extinctionTime
        (le_trans (by exact_mod_cast Nat.sub_le n (k₀ + j)) hn)
    have hu := hM (n - (k₀ + j)) (Nat.sub_le _ _)
    nlinarith
  apply (expectedCount_block_bound hn hblock hA hA0 hborn (sq_pos_of_pos hM0) hp hpos).trans
  apply add_le_add le_rfl
  calc
    M ^ 2 / (attachmentSteps x n k₀ m).card ≤ M ^ 2 / (((m : ℝ) - M) / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg M) hden hcount
    _ = _ := by rw [div_div_eq_mul_div]; ring

end Freezing2.TrackedClusters
