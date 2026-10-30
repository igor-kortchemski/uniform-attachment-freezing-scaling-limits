module

public import Freezing2.Geometry.FiniteChaining
public import Freezing2.Probability.CoalescenceMetric

/-!
# Chaining in the actual finite coalescence metric

This is the deterministic triangle-inequality step of U31, on the full-measure
event supplied by the actual reverse history. Probabilistic estimates for the
successive block errors and the last net are separate obligations.
-/

@[expose] public section

open MeasureTheory
open scoped Classical BigOperators

namespace Freezing2.ReverseCoalescence

open Freezing1 Freezing2.ReverseHistory

/-- Every actual finite history satisfying the proved metric laws supports
dyadic chaining, with repeated samples allowed and the final net retained. -/
theorem jointLaw_coalescence_cover_chaining (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x)
    (v : ℕ → {u // u ∈ Freezing1.vertexLabels x n})
    (ε : ℕ → ℝ) (k m : ℕ) (r : ℝ)
    (hε : ∀ j < m, 0 ≤ ε (k + j)) :
    ∀ᵐ ω ∂jointLaw x n,
      (∀ j < m, ∀ i, 2 ^ (k + j) ≤ i → i < 2 ^ (k + j + 1) →
        ∃ l < 2 ^ (k + j), coalescenceDistance n (v i).val (v l).val ω ≤ ε (k + j)) →
      (∀ u ∈ Freezing1.vertexLabels x n, ∃ i < 2 ^ (k + m),
        coalescenceDistance n u (v i).val ω ≤ r) →
      ∀ u ∈ Freezing1.vertexLabels x n, ∃ l < 2 ^ k,
        coalescenceDistance n u (v l).val ω ≤
          (∑ j ∈ Finset.range m, ε (k + j)) + r := by
  filter_upwards [jointLaw_exists_coalescenceMetric x n hn] with ω hmetric
  obtain ⟨metric, hdist⟩ := hmetric
  let := metric
  intro hstep hcover u hu
  have hs : ∀ j < m, ∀ i, 2 ^ (k + j) ≤ i → i < 2 ^ (k + j + 1) →
      ∃ l < 2 ^ (k + j), dist (v i) (v l) ≤ ε (k + j) := by
    simpa only [hdist] using hstep
  have hc : ∀ a ∈ (Set.univ : Set {u // u ∈ Freezing1.vertexLabels x n}),
      ∃ i < 2 ^ (k + m), dist a (v i) ≤ r := by
    intro a _
    simpa only [hdist] using hcover a.val a.property
  simpa only [hdist] using dyadic_cover_chaining v ε k m hε hs hc ⟨u, hu⟩ (Set.mem_univ _)

end Freezing2.ReverseCoalescence
