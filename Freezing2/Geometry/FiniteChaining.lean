module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite dyadic sample chaining

The deterministic part of source U31. Every newly added dyadic block is
close to the preceding sample prefix; chaining these witnesses bounds the
distance to the initial prefix. A final finite-net error is retained.
No probabilistic block estimate is assumed to have been proved here.
-/

@[expose] public section

open scoped BigOperators

namespace Freezing2

variable {X : Type*} [PseudoMetricSpace X]

/-- A sequence of bounds on the newly added dyadic blocks controls every
point in the last sample prefix by the sum of the intervening bounds. -/
theorem dyadic_sample_chaining (v : ℕ → X) (ε : ℕ → ℝ) (k m : ℕ)
    (hε : ∀ j < m, 0 ≤ ε (k + j))
    (hstep : ∀ j < m, ∀ i, 2 ^ (k + j) ≤ i → i < 2 ^ (k + j + 1) →
      ∃ l < 2 ^ (k + j), dist (v i) (v l) ≤ ε (k + j)) :
    ∀ i < 2 ^ (k + m), ∃ l < 2 ^ k,
      dist (v i) (v l) ≤ ∑ j ∈ Finset.range m, ε (k + j) := by
  induction m with
  | zero =>
      intro i hi
      refine ⟨i, by simpa using hi, ?_⟩
      simp
  | succ m ih =>
      intro i hi
      have hprev : ∃ l < 2 ^ (k + m), dist (v i) (v l) ≤ ε (k + m) := by
        by_cases hold : i < 2 ^ (k + m)
        · exact ⟨i, hold, by simpa using hε m (Nat.lt_succ_self m)⟩
        · exact hstep m (Nat.lt_succ_self m) i (Nat.le_of_not_gt hold)
            (by simpa only [Nat.add_assoc] using hi)
      obtain ⟨l, hl, hil⟩ := hprev
      obtain ⟨a, ha, hla⟩ := ih (fun j hj ↦ hε j (Nat.lt_succ_of_lt hj))
        (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj)) l hl
      refine ⟨a, ha, ?_⟩
      rw [Finset.sum_range_succ]
      exact (dist_triangle (v i) (v l) (v a)).trans (by linarith)

/-- Finite chaining with the last-net error. The covered set may be the
whole carrier, and coincident sample points are allowed. -/
theorem dyadic_cover_chaining (v : ℕ → X) (ε : ℕ → ℝ) (k m : ℕ)
    (hε : ∀ j < m, 0 ≤ ε (k + j))
    (hstep : ∀ j < m, ∀ i, 2 ^ (k + j) ≤ i → i < 2 ^ (k + j + 1) →
      ∃ l < 2 ^ (k + j), dist (v i) (v l) ≤ ε (k + j))
    {T : Set X} {r : ℝ}
    (hcover : ∀ x ∈ T, ∃ i < 2 ^ (k + m), dist x (v i) ≤ r) :
    ∀ x ∈ T, ∃ l < 2 ^ k,
      dist x (v l) ≤ (∑ j ∈ Finset.range m, ε (k + j)) + r := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hcover x hx
  obtain ⟨l, hl, hil⟩ := dyadic_sample_chaining v ε k m hε hstep i hi
  exact ⟨l, hl, (dist_triangle x (v i) (v l)).trans (by linarith)⟩

end Freezing2
