module

public import Freezing2.Probability.SupercriticalDistanceApproximation
public import Mathlib.Probability.Independence.Basic

/-!
# The corrected finite star-matrix approximation

All entries use one actual reverse tree and one independent vector of iid
uniform labels. The comparison matrix is zero on the index diagonal, as
required by a distance matrix, and is the sum of the two branches elsewhere.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

/-- One reverse history and a vector of `k` independent uniform source labels. -/
noncomputable def sampledReverseVectorLaw (x : ℕ → ℤ) (n k : ℕ) :
    Measure (History × (Fin k → VertexLabel)) :=
  (jointLaw (companionSchedule x) n).prod
    (Measure.pi (fun _ : Fin k ↦ uniformVertex x n))

theorem sampledReverseVectorLaw_probability (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : SurvivesThrough x n) : IsProbabilityMeasure (sampledReverseVectorLaw x n k) := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  unfold sampledReverseVectorLaw
  infer_instance

/-- Distinct sample coordinates have precisely the two-sample law used by N10;
the labels themselves may coincide. -/
theorem sampledReverseVectorLaw_map_pair (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : SurvivesThrough x n) {i j : Fin k} (hij : i ≠ j) :
    (sampledReverseVectorLaw x n k).map (fun q ↦ (q.1, (q.2 i, q.2 j))) =
      sampledReverseLaw x n := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hi := iIndepFun_pi (μ := fun _ : Fin k ↦ uniformVertex x n)
    (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hm := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).map_eq,
    (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) j).map_eq] at hm
  unfold sampledReverseVectorLaw sampledReverseLaw
  change Measure.map (Prod.map id (fun v : Fin k → VertexLabel ↦ (v i, v j))) _ = _
  rw [← Measure.map_prod_map _ _ measurable_id
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)), Measure.map_id, hm]

/-- The scaled graph-distance matrix of the common actual reverse tree. -/
noncomputable def sampledDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) : Fin k → Fin k → ℝ :=
  fun i j ↦ (n : ℝ) ^ (α - 1) * reverseDistance n (q.2 i) (q.2 j) q.1

/-- The corrected star target has an exact zero diagonal. -/
noncomputable def sampledStarMatrix (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) : Fin k → Fin k → ℝ :=
  fun i j ↦ if i = j then 0 else sampledBranchSum x α n (q.2 i) (q.2 j)

@[simp] theorem sampledDistanceMatrix_diag (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) (i : Fin k) :
    sampledDistanceMatrix α n k q i i = 0 := by
  simp [sampledDistanceMatrix, reverseDistance]

@[simp] theorem sampledStarMatrix_diag (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) (i : Fin k) :
    sampledStarMatrix x α n k q i i = 0 := by
  simp [sampledStarMatrix]

theorem measurable_sampledDistanceMatrix (α : ℝ) (n k : ℕ) :
    Measurable (sampledDistanceMatrix α n k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  apply measurable_from_prod_countable_left
  intro v
  exact (measurable_reverseDistance n (v i) (v j)).const_mul _

theorem measurable_sampledStarMatrix (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ) :
    Measurable (sampledStarMatrix x α n k) := by
  exact (show Measurable (fun v : Fin k → VertexLabel ↦
    fun i j ↦ if i = j then (0 : ℝ) else sampledBranchSum x α n (v i) (v j)) from
    measurable_of_countable _).comp measurable_snd

theorem sampled_matrix_distance_gt_iff (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) {ε : ℝ} (hε : 0 ≤ ε) :
    ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q) ↔
      ∃ p : Fin k × Fin k, ε <
        |sampledDistanceMatrix α n k q p.1 p.2 - sampledStarMatrix x α n k q p.1 p.2| := by
  rw [← not_le, dist_pi_le_iff hε]
  simp only [dist_pi_le_iff hε, Real.dist_eq, not_forall, not_le, Prod.exists]

theorem sampled_matrix_entry_error_probability_le
    (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ) (hx : IsSigned (x n))
    (hs : SurvivesThrough (x n) n) (p : Fin k × Fin k) {ε : ℝ} (hε : 0 ≤ ε) :
    (sampledReverseVectorLaw (x n) n k).real
      {q | ε < |sampledDistanceMatrix α n k q p.1 p.2 -
        sampledStarMatrix x α n k q p.1 p.2|} ≤
      (sampledReverseLaw (x n) n).real (sampledBranchErrorEvent x α n ε) := by
  by_cases hp : p.1 = p.2
  · simp only [hp, sampledDistanceMatrix_diag, sampledStarMatrix_diag, sub_zero, abs_zero]
    simp only [not_lt.mpr hε, ofPred_false, measureReal_empty]
    exact measureReal_nonneg
  · have hm := sampledReverseVectorLaw_map_pair (x n) hx hs hp
    have hh := congrArg (fun μ : Measure (History × (VertexLabel × VertexLabel)) ↦
      μ (sampledBranchErrorEvent x α n ε)) hm
    have hmeas : Measurable (fun q : History × (Fin k → VertexLabel) ↦ (q.1, (q.2 p.1, q.2 p.2))) := by
      fun_prop
    rw [Measure.map_apply hmeas
      (measurableSet_sampledBranchErrorEvent x α n ε)] at hh
    apply le_of_eq
    exact congrArg ENNReal.toReal (by
      simpa only [sampledBranchErrorEvent, sampledDistanceMatrix, sampledStarMatrix,
        hp, ↓reduceIte, preimage_ofPred_eq] using hh)

/-- For every fixed `k`, the maximum entry error tends to zero in probability
under the genuine joint tree-and-iid-sample law. The zero diagonal is exact. -/
theorem tendsto_sampledStarMatrix_error_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseVectorLaw (x n) n k).real
      {q | ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)})
      atTop (𝓝 0) := by
  have hp := tendsto_sampledBranchError_probability hx hαhalf hα1 hL1 hpos h2 hε
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _
    (show Tendsto (fun n ↦ (Fintype.card (Fin k × Fin k) : ℝ) *
      (sampledReverseLaw (x n) n).real (sampledBranchErrorEvent x α n ε)) atTop (𝓝 0) from
      by simpa using hp.const_mul (Fintype.card (Fin k × Fin k) : ℝ))
  intro n
  let := sampledReverseVectorLaw_probability (x n) (hx n).1 (k := k) (hx n).2
  have hset : {q | ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)} =
      ⋃ p : Fin k × Fin k, {q | ε < |sampledDistanceMatrix α n k q p.1 p.2 -
        sampledStarMatrix x α n k q p.1 p.2|} := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion, sampled_matrix_distance_gt_iff x α n k q hε.le]
  rw [hset]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _p : Fin k × Fin k, (sampledReverseLaw (x n) n).real
        (sampledBranchErrorEvent x α n ε) := by
      apply Finset.sum_le_sum
      intro p _
      exact sampled_matrix_entry_error_probability_le x α n k (hx n).1 (hx n).2 p hε.le
    _ = _ := by simp

/-- The paper-facing reciprocal-profile statement, with only positive rows
required to be admissible and with the approved zero-diagonal correction. -/
theorem tendsto_sampledStarMatrix_error_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseVectorLaw (x n) n k).real
      {q | ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)})
      atTop (𝓝 0) := by
  apply (tendsto_sampledStarMatrix_error_probability (admissible_initialRowExtension hx)
    hαhalf hα1 (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) k hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  have heq : sampledStarMatrix (initialRowExtension x) α n k = sampledStarMatrix x α n k := by
    funext q i j
    simp only [sampledStarMatrix, sampledBranchSum, normalizedHarmonicPrefix, hn]
  rw [hn, heq]

end Freezing2
