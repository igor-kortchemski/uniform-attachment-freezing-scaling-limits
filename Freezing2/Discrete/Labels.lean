module

public import Freezing2.Discrete.Walk
public import Mathlib.Data.Finset.Sum
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Distributions.Uniform

/-!
# Deterministic vertex labels and uniform birth times

Frozen labels carry their freezing time; active labels are distinguished from
frozen labels by a disjoint sum. This is a concrete version of the paper's
`𝕍ₙ = 𝔽ₙ ∪ 𝔸ₙ` (equation `eq:labels`). The active labels carry exactly the indices `1,…,Sₙ`, as in the paper.
-/

@[expose] public section

namespace Freezing2

/-- Left labels are frozen times; right labels distinguish currently active vertices. -/
abbrev VertexLabel := ℕ ⊕ ℕ

instance : MeasurableSingletonClass VertexLabel := by
  constructor
  intro v
  cases v <;> apply measurableSet_sum_iff.mpr <;> constructor <;> simp

/-- The deterministic set of labels of the growth-coalescent tree at time `n`. -/
def vertexLabels (x : ℕ → ℤ) (n : ℕ) : Finset VertexLabel :=
  (downSteps x 0 n).disjSum (Finset.Ioc 0 (activeCount x n).toNat)

/-- The time at which a label appears when the growth-coalescent is read backwards. -/
def birthTime (n : ℕ) : VertexLabel → ℕ
  | .inl i => i - 1
  | .inr _ => n

@[simp] theorem birthTime_frozen (n i : ℕ) : birthTime n (.inl i) = i - 1 := rfl

@[simp] theorem birthTime_active (n i : ℕ) : birthTime n (.inr i) = n := rfl

/-- Every label has appeared by time `n`. -/
theorem birthTime_le (x : ℕ → ℤ) {n : ℕ} {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) : birthTime n v ≤ n := by
  cases v with
  | inl i =>
    simp only [vertexLabels, Finset.inl_mem_disjSum, downSteps,
      Finset.mem_filter, Finset.mem_Ioc] at hv
    simp only [birthTime]
    omega
  | inr i => exact le_rfl

/-- The deterministic labels have the same vertex count as the forward attachment process. -/
theorem vertexLabels_card (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (h : 0 ≤ activeCount x n) :
    (vertexLabels x n).card = (upSteps x 0 n).card + 1 := by
  simpa [vertexLabels] using frozen_add_active_eq_vertex_count x hx h

/-- In particular, this label space is nonempty even if no active vertices remain. -/
theorem vertexLabels_nonempty (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (h : 0 ≤ activeCount x n) : (vertexLabels x n).Nonempty := by
  apply Finset.card_pos.mp
  rw [vertexLabels_card x hx h]
  omega

/-- The labels born strictly before `m ≤ n` are exactly the frozen labels through time `m`. -/
theorem early_vertexLabels (x : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    (vertexLabels x n).filter (fun v => birthTime n v < m) =
      (downSteps x 0 m).map Function.Embedding.inl := by
  apply Finset.ext
  intro v
  rw [Finset.mem_filter]
  cases v with
  | inl i =>
    simp only [Finset.mem_filter, vertexLabels, Finset.inl_mem_disjSum,
      downSteps, Finset.mem_Ioc, birthTime, Finset.mem_map, Function.Embedding.inl_apply,
      Sum.inl.injEq, exists_eq_right]
    omega
  | inr i =>
    simp only [vertexLabels, Finset.inr_mem_disjSum,
      Finset.mem_Ioc, birthTime, Finset.mem_map, Function.Embedding.inl_apply,
      Sum.inl_ne_inr, and_false, exists_false, iff_false, not_and]
    omega

/-- Exact counting numerator for Lemma `lem:bunif`. -/
theorem early_vertexLabels_card (x : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    ((vertexLabels x n).filter (fun v => birthTime n v < m)).card =
      (downSteps x 0 m).card := by
  rw [early_vertexLabels x hmn, Finset.card_map]

/-- The uniform measure on the paper's deterministic vertex-label set. -/
noncomputable def uniformVertex (x : ℕ → ℤ) (n : ℕ) : MeasureTheory.Measure VertexLabel :=
  MeasureTheory.Measure.uniformOfFinset (vertexLabels x n)

/-- Uniformly sampling the nonempty label space gives a probability measure. -/
theorem uniformVertex_isProbabilityMeasure (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (h : 0 ≤ activeCount x n) : MeasureTheory.IsProbabilityMeasure (uniformVertex x n) := by
  constructor
  rw [uniformVertex, MeasureTheory.Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (vertexLabels_nonempty x hx h).card_pos.ne')
    (by simp)

/-- Uniform birth-time distribution as a ratio of finite counts. -/
theorem uniformVertex_birth_lt_count (x : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    (uniformVertex x n).real {v | birthTime n v < m} =
      ((downSteps x 0 m).card : ℝ) / (vertexLabels x n).card := by
  rw [MeasureTheory.Measure.real, uniformVertex,
    MeasureTheory.Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, early_vertexLabels_card x hmn,
    ENNReal.toReal_div, ENNReal.toReal_natCast]

/-- Lemma `lem:bunif`: the exact birth-time law of a uniform vertex.

The survival boundary is expressed by the weaker sufficient condition `0 ≤ Sₙ`;
the source's `n ≤ τ` guarantees this for a signed walk started at one.
-/
theorem uniformVertex_birth_lt (x : ℕ → ℤ) (hx : IsSigned x) {m n : ℕ}
    (hmn : m ≤ n) (hn : 0 ≤ activeCount x n) :
    (uniformVertex x n).real {v | birthTime n v < m} =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [uniformVertex_birth_lt_count x hmn, vertexLabels_card x hx hn]
  have hm : 2 * ((downSteps x 0 m).card : ℝ) = (m : ℝ) + 1 - activeCount x m := by
    exact_mod_cast twice_frozen_count x hx m
  have hn' : 2 * (((upSteps x 0 n).card : ℝ) + 1) = (n : ℝ) + 1 + activeCount x n := by
    exact_mod_cast twice_vertex_count x hx n
  rw [← hm, ← hn']
  push_cast
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- Birth law with the source's finite "at or before extinction" condition made explicit. -/
theorem uniformVertex_birth_lt_before_extinction (x : ℕ → ℤ) (hx : IsSigned x)
    {m n : ℕ} (hmn : m ≤ n)
    (hzero : ∀ k, k < n → activeCount x k ≠ 0) :
    (uniformVertex x n).real {v | birthTime n v < m} =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) :=
  uniformVertex_birth_lt x hx hmn (activeCount_nonneg_of_no_zero_before x hx n hzero)

end Freezing2
