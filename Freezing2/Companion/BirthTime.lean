module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.Path
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Sum

/-!
# Deterministic vertex labels and the uniform birth-time law

The labels of Algorithm 2 are deterministic. `Sum.inl j` represents active label
`a_(j+1)`; `Sum.inr i` represents frozen label `i+1`. The latter vertex is born
at reverse time `i`, so its birth time is one less than its paper label.

This file proves the uniform law of Lemma `lem:bunif` directly on this label
set, including the extinction endpoint `S_n = 0`. It does not construct the
random forest or prove its law agrees with Algorithm 1.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Freezing1

instance instMeasurableSingletonVertexLabel : MeasurableSingletonClass (ℕ ⊕ ℕ) where
  measurableSet_singleton v := by
    cases v with
    | inl i => simpa only [Set.image_singleton] using
        (measurableSet_singleton i).inl_image (β := ℕ)
    | inr i => simpa only [Set.image_singleton] using
        (measurableSet_singleton i).inr_image (α := ℕ)

/-- Zero-based indices of freezing steps among the first `n` steps. -/
def frozenIndices (x : SignSequence) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun i => x (i + 1) = false

/-- The deterministic label set in equation `eq:labels`, with disjoint tags. -/
def vertexLabels (x : SignSequence) (n : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (Finset.range (activeCount x n).toNat).disjSum (frozenIndices x n)

/-- Birth time in Algorithm 2: active labels are born at `n`, frozen label
`i+1` is born at `i`. Values outside `vertexLabels` are not used. -/
def birthTime (n : ℕ) : ℕ ⊕ ℕ → ℕ
  | .inl _ => n
  | .inr i => i

/-- A uniformly chosen vertex of the deterministic label set. -/
noncomputable def uniformVertex (x : SignSequence) (n : ℕ) : Measure (ℕ ⊕ ℕ) :=
  Measure.uniformOfFinset (vertexLabels x n)

theorem card_frozenIndices (x : SignSequence) (n : ℕ) :
    (frozenIndices x n).card = minusCount x n := by
  have h : (frozenIndices x n).card + plusCount x n = n := by
    rw [frozenIndices, Finset.card_eq_sum_ones, Finset.sum_filter, plusCount,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range n, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        cases x (i + 1) <;> simp
      _ = n := by simp
  unfold minusCount
  omega

/-- Active and frozen labels together give exactly `1 + p_n` vertices. -/
theorem card_vertexLabels {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) :
    (vertexLabels x n).card = plusCount x n + 1 := by
  simp only [vertexLabels, Finset.card_disjSum, Finset.card_range, card_frozenIndices]
  have h := activeCount_eq_counts x n
  have hnat := Int.toNat_of_nonneg hn
  omega

theorem vertexLabels_nonempty {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) : (vertexLabels x n).Nonempty := by
  rw [← Finset.card_pos, card_vertexLabels hn]
  omega

/-- The displayed vertex-count identity in Section 2.1. -/
theorem card_vertexLabels_real {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) :
    ((vertexLabels x n).card : ℝ) = ((activeCount x n : ℝ) + n + 1) / 2 := by
  rw [card_vertexLabels hn]
  have h : (activeCount x n : ℝ) = 1 + 2 * (plusCount x n : ℝ) - n := by
    exact_mod_cast activeCount_eq x n
  push_cast
  linarith

theorem uniformVertex_isProbabilityMeasure {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) : IsProbabilityMeasure (uniformVertex x n) := by
  constructor
  rw [uniformVertex, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (vertexLabels_nonempty hn).card_pos.ne')
    (by simp)

theorem birthTime_filter {x : SignSequence} {m n : ℕ} (hmn : m ≤ n) :
    (vertexLabels x n).filter (fun v => birthTime n v < m) =
      (∅ : Finset ℕ).disjSum (frozenIndices x m) := by
  apply Finset.ext
  intro v
  cases v with
  | inl j =>
    constructor
    · intro hv
      have hv' := (Finset.mem_filter.mp hv).2
      exact False.elim ((not_lt_of_ge hmn) hv')
    · intro hv
      simp at hv
  | inr i =>
    constructor
    · intro hv
      obtain ⟨hv, him⟩ := Finset.mem_filter.mp hv
      have hf : i ∈ frozenIndices x n := Finset.inr_mem_disjSum.mp hv
      obtain ⟨hin, hx⟩ := Finset.mem_filter.mp hf
      apply Finset.inr_mem_disjSum.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr him, hx⟩
    · intro hv
      have hf : i ∈ frozenIndices x m := Finset.inr_mem_disjSum.mp hv
      obtain ⟨him, hx⟩ := Finset.mem_filter.mp hf
      have him' := Finset.mem_range.mp him
      apply Finset.mem_filter.mpr
      refine ⟨Finset.inr_mem_disjSum.mpr ?_, him'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (him'.trans_le hmn), hx⟩

/-- Lemma `lem:bunif`, first expressed as a ratio of exact finite counts. -/
theorem uniform_birthTime_lt_counts {x : SignSequence} {m n : ℕ}
    (hn : 0 ≤ activeCount x n) (hmn : m ≤ n) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      (minusCount x m : ℝ) / (plusCount x n + 1 : ℝ) := by
  rw [uniformVertex, Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  rw [birthTime_filter hmn, Finset.card_disjSum, Finset.card_empty, zero_add,
    card_frozenIndices, card_vertexLabels hn]
  simp [ENNReal.toReal_add]

/-- The exact probability formula of Lemma `lem:bunif`. The only endpoint
condition needed for the deterministic-label law is `S_n ≥ 0`; before or at
extinction this follows from the walk. -/
theorem uniform_birthTime_lt {x : SignSequence} {m n : ℕ}
    (hn : 0 ≤ activeCount x n) (hmn : m ≤ n) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [uniform_birthTime_lt_counts hn hmn]
  have hm : (activeCount x m : ℝ) = 1 + (plusCount x m : ℝ) - minusCount x m := by
    exact_mod_cast activeCount_eq_counts x m
  have hn' : (activeCount x n : ℝ) = 1 + 2 * (plusCount x n : ℝ) - n := by
    exact_mod_cast activeCount_eq x n
  have hc : (plusCount x m : ℝ) + minusCount x m = m := by
    exact_mod_cast plusCount_add_minusCount x m
  have hnum : (m : ℝ) + 1 - activeCount x m = 2 * minusCount x m := by linarith
  have hden : (n : ℝ) + 1 + activeCount x n = 2 * (plusCount x n + 1) := by linarith
  rw [hnum, hden, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

end Freezing1
