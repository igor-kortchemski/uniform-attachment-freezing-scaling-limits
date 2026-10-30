module

public import Freezing2.Probability.OldestIsolation
public import Freezing2.Probability.TrackedClusterBlock

/-!
# Nonmerger of the oldest marked vertex over an actual reverse-time block

This combines the proved birth-order comparison and actual count recurrence.
The nonnegative target phase and all-born initial phase are explicit, avoiding
the manuscript's undefined negative forest phase at block index zero.
-/

@[expose] public section

namespace Freezing2.TrackedClusters

open Freezing1

/-- A quantitative oldest-isolation bound in the actual process. The block
starts at source phase `t + m` and ends at phase `t`. -/
theorem oldest_isolation_probability_le_block_bound {x : SignSequence}
    {n t m : ℕ} (hn : (n : ℕ∞) ≤ extinctionTime x) (hblock : t + m ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    {u : ℕ ⊕ ℕ} (hu : u ∈ A)
    (holdest : ∀ v ∈ A, Freezing1.birthTime n v ≤ Freezing1.birthTime n u)
    (hborn : ∀ v ∈ A, t + m ≤ Freezing1.birthTime n v)
    {M : ℝ} (hM0 : 0 < M) (hM : ∀ s ≤ n, (Freezing1.activeCount x s : ℝ) ≤ M)
    (hm : M < m) :
    (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} ≤
      (1 + 2 * M ^ 2 / ((m : ℝ) - M)) / A.card := by
  have ht : t ≤ n := by omega
  have he : n - (t + m) + m = n - t := by omega
  have hborn' : ∀ v ∈ A, n - (n - (t + m)) ≤ Freezing1.birthTime n v := by
    simpa only [Nat.sub_sub_self hblock] using hborn
  have hc := expectedCount_block_bound_of_population_bound hn
    (show n - (t + m) + m ≤ n by omega) hA ⟨u, hu⟩ hborn' hM0 hM hm
  rw [he] at hc
  exact (oldest_isolation_probability_le_expectedCount hn ht hA hu holdest
    (fun v hv ↦ (Nat.le_add_right t m).trans (hborn v hv))).trans
      (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _))

end Freezing2.TrackedClusters
