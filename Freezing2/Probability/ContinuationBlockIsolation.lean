module

public import Freezing2.Probability.ContinuationIsolation
public import Freezing2.Probability.ContinuationCount
public import Freezing2.Analysis.TightnessBlockArithmetic

/-!
# Uniform isolation bounds for actual continuation kernels

The older label is compared with younger labels born during continuation.
The count contraction is applied only in the final interval, after every
marked label has appeared. These bounds are uniform over the valid initial
forest, so a separate actual-history conditional identity can apply them.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace Freezing2.ReverseContinuation

open Freezing1 Freezing2.TrackedClusters

/-- Start at phase s, wait until all marks are born by r, and contract counts
over the remaining interval down to t. The intermediate law is not replaced
by an unconditional marginal. -/
theorem oldest_isolation_probability_le_block_bound {x : SignSequence}
    {n s r t : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hr : r ≤ s) (ht : t ≤ r)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) {u : ℕ ⊕ ℕ} (hu : u ∈ A)
    (huBorn : s ≤ Freezing1.birthTime n u)
    (hyoung : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v ≤ s)
    (hboundary : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v = s → Alone F A v)
    (hborn : ∀ v ∈ A, r ≤ Freezing1.birthTime n v)
    {B : ℝ} (hB : 0 < B) (hpop : ∀ i ≤ n, (Freezing1.activeCount x i : ℝ) ≤ B)
    (hgap : B < (r - t : ℕ)) :
    (law x s F (s - t)).real {G | Alone G A u} ≤
      (1 + 2 * B ^ 2 / ((r - t : ℕ) - B)) / A.card := by
  have he : s - r + (r - t) = s - t := by omega
  have hblock : s - r + (r - t) ≤ s := by omega
  have hborn' : ∀ v ∈ A, s - (s - r) ≤ Freezing1.birthTime n v := by
    simpa only [Nat.sub_sub_self hr] using hborn
  have hc := expectedCountFrom_block_bound_of_population_bound hn hs hblock hF
    hA ⟨u, hu⟩ hborn' hB hpop hgap
  rw [he] at hc
  have hi := oldest_isolation_probability_le_integral_count hn hs (ht.trans hr) hF
    hA hu huBorn hyoung hboundary (fun v hv ↦ ht.trans (hborn v hv))
  exact hi.trans (div_le_div_of_nonneg_right hc (Nat.cast_nonneg _))

/-- The kernel contraction factor used in alternating critical blocks.
The final all-born interval may be longer than the manuscript's factor-four
block, as in the repaired factor-sixteen occupancy construction. -/
theorem oldest_isolation_kernel_le_three_quarters {x : SignSequence}
    {n k K s r t : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : 0 < k) (hkn : k ≤ n)
    (hs : s ≤ n) (hr : r ≤ s) (ht : t ≤ r) (hF : Reverse.ValidAt x n s F)
    {M : ℝ} (hM : 0 < M) (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (Freezing1.activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hlength : tightnessBlockLength M n k ≤ r - t)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    (hcard : A.card = K + 1) (hK : M * Real.sqrt k ≤ K)
    {u : ℕ ⊕ ℕ} (hu : u ∈ A) (huBorn : s ≤ Freezing1.birthTime n u)
    (hyoung : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v ≤ s)
    (hboundary : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v = s → Alone F A v)
    (hborn : ∀ v ∈ A, r ≤ Freezing1.birthTime n v) :
    (law x s F (s - t)).real {G | Alone G A u} ≤ (3 / 4 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  have hB : 0 < M * Real.sqrt n := mul_pos hM (Real.sqrt_pos.mpr hnR)
  have ha : 0 < M * Real.sqrt k := by linarith
  have hK0 : 0 < K := by exact_mod_cast ha.trans_le hK
  have hlen : (tightnessBlockLength M n k : ℝ) ≤ (r - t : ℕ) := by exact_mod_cast hlength
  have hgap₀ := tightnessBlockLength_gap hM hk hkn
  have hgap : 3 * (M * Real.sqrt n) ^ 2 ≤
      (M * Real.sqrt k) * ((r - t : ℕ) - M * Real.sqrt n) := by
    exact hgap₀.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hlen _) ha.le)
  have hm : M * Real.sqrt n < (r - t : ℕ) := by
    by_contra h
    have hp := mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr (le_of_not_gt h))
    nlinarith [sq_pos_of_pos hB]
  have h := oldest_isolation_probability_le_block_bound hn hs hr ht hF hA hu huBorn
    hyoung hboundary hborn hB hpop hm
  rw [hcard, Nat.cast_add, Nat.cast_one] at h
  apply (h.trans (one_block_isolation_numeric_bound hB hlarge hgap hK0)).trans
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)).mpr
  linarith

end Freezing2.ReverseContinuation
