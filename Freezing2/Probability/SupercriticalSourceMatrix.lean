module

public import Freezing2.Probability.SupercriticalDistanceLimit
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Source indices for the corrected supercritical reverse-tree limit

The index set is literally `Fin (k + 1)`: index zero is the root and successors
are the `k` independent uniform samples. The observed matrix is the actual
graph distance divided by `n ^ (1 - α)` almost surely. The limiting matrix has
zero diagonal and the sum of two source branch integrals off the diagonal.
Transport to the forward construction is kept separate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

/-- Write the distinguished root first, followed by the sampled coordinates. -/
def sourceMatrixReindex (k : ℕ) (M : Option (Fin k) → Option (Fin k) → ℝ) :
    Fin (k + 1) → Fin (k + 1) → ℝ :=
  fun i j ↦ M (finSuccEquiv k i) (finSuccEquiv k j)

theorem continuous_sourceMatrixReindex (k : ℕ) : Continuous (sourceMatrixReindex k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (finSuccEquiv k j)).comp (continuous_apply (finSuccEquiv k i))

def sourceBranchCoordinate {k : ℕ} (b : Fin k → ℝ) (i : Fin (k + 1)) : ℝ :=
  rootAugmentedBranch b (finSuccEquiv k i)

@[simp] theorem sourceBranchCoordinate_zero {k : ℕ} (b : Fin k → ℝ) :
    sourceBranchCoordinate b 0 = 0 := by simp [sourceBranchCoordinate, rootAugmentedBranch]

@[simp] theorem sourceBranchCoordinate_succ {k : ℕ} (b : Fin k → ℝ) (i : Fin k) :
    sourceBranchCoordinate b i.succ = b i := by simp [sourceBranchCoordinate, rootAugmentedBranch]

/-- The corrected matrix in the Introduction's indexing convention. -/
def sourceStarMatrixMap {k : ℕ} (b : Fin k → ℝ) : Fin (k + 1) → Fin (k + 1) → ℝ :=
  sourceMatrixReindex k (rootedStarMatrixMap b)

theorem sourceStarMatrixMap_eq_starDistance {k : ℕ} (b : Fin k → ℝ) :
    sourceStarMatrixMap b = Audit.starDistance (sourceBranchCoordinate b) := by
  funext i j
  simp only [sourceStarMatrixMap, sourceMatrixReindex, rootedStarMatrixMap_eq_starDistance,
    Audit.starDistance, sourceBranchCoordinate, Equiv.apply_eq_iff_eq]

@[simp] theorem sourceStarMatrixMap_diag {k : ℕ} (b : Fin k → ℝ) (i : Fin (k + 1)) :
    sourceStarMatrixMap b i i = 0 := by
  rw [sourceStarMatrixMap_eq_starDistance]
  exact Audit.starDistance_self _ _

theorem sourceStarMatrixMap_offDiag {k : ℕ} (b : Fin k → ℝ)
    {i j : Fin (k + 1)} (hij : i ≠ j) :
    sourceStarMatrixMap b i j = sourceBranchCoordinate b i + sourceBranchCoordinate b j := by
  rw [sourceStarMatrixMap_eq_starDistance]
  simp [Audit.starDistance, hij]

theorem continuous_sourceStarMatrixMap (k : ℕ) : Continuous (sourceStarMatrixMap (k := k)) :=
  (continuous_sourceMatrixReindex k).comp (continuous_rootedStarMatrixMap k)

def sourceSampledVertex {k : ℕ} (n : ℕ) (q : History × (Fin k → VertexLabel))
    (i : Fin (k + 1)) : ℕ ⊕ ℕ := rootAugmentedLabel n q (finSuccEquiv k i)

@[simp] theorem sourceSampledVertex_zero {k : ℕ} (n : ℕ)
    (q : History × (Fin k → VertexLabel)) :
    sourceSampledVertex n q 0 = reverseTerminalRoot n q.1 := by
  simp [sourceSampledVertex, rootAugmentedLabel]

@[simp] theorem sourceSampledVertex_succ {k : ℕ} (n : ℕ)
    (q : History × (Fin k → VertexLabel)) (i : Fin k) :
    sourceSampledVertex n q i.succ = toCompanionLabel (q.2 i) := by
  simp [sourceSampledVertex, rootAugmentedLabel]

noncomputable def sourceSampledDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) : Fin (k + 1) → Fin (k + 1) → ℝ :=
  sourceMatrixReindex k (rootedSampledDistanceMatrix α n k q)

theorem heightScale_eq_inv_heightNormalization (n : ℕ) (α : ℝ) :
    (n : ℝ) ^ (α - 1) = 1 / (n : ℝ) ^ (1 - α) := by
  rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- Every source-indexed entry is a distance in the actual terminal graph,
with the literal normalization displayed in the paper. -/
theorem sourceSampledDistanceMatrix_eq_graphDistance
    (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ} (hs : SurvivesThrough x n) (α : ℝ) :
    ∀ᵐ q ∂sampledReverseVectorLaw x n k, ∀ i j,
      sourceSampledDistanceMatrix α n k q i j =
        ((forestAt n 0 q.1).graph.dist (sourceSampledVertex n q i)
          (sourceSampledVertex n q j) : ℝ) / (n : ℝ) ^ (1 - α) := by
  filter_upwards [rootedSampledDistanceMatrix_eq_graphDistance x hx hs α] with q hq
  intro i j
  change rootedSampledDistanceMatrix α n k q (finSuccEquiv k i) (finSuccEquiv k j) = _
  rw [hq, heightScale_eq_inv_heightNormalization]
  simp only [sourceSampledVertex, div_eq_mul_inv, one_mul, mul_comm]

noncomputable def sourceSampledDistanceLaw (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : SurvivesThrough (x n) n) :
    ProbabilityMeasure (Fin (k + 1) → Fin (k + 1) → ℝ) :=
  (rootedSampledDistanceLaw x α n k hx hs).map (sourceMatrixReindex k)

theorem sourceSampledDistanceLaw_eq_map (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : SurvivesThrough (x n) n) :
    sourceSampledDistanceLaw x α n k hx hs =
      (sampledReverseVectorProbability (x n) n k hx hs).map (sourceSampledDistanceMatrix α n k) := by
  apply Subtype.ext
  change ((sampledReverseVectorLaw (x n) n k).map (rootedSampledDistanceMatrix α n k)).map
    (sourceMatrixReindex k) = _
  rw [Measure.map_map (continuous_sourceMatrixReindex k).measurable
    (measurable_rootedSampledDistanceMatrix α n k)]
  rfl

theorem iidSourceBranchLimit_map_sourceStar (f : ℝ → ℝ) (k : ℕ) :
    ((iidSourceBranchLimit f k).map rootedStarMatrixMap).map (sourceMatrixReindex k) =
      (iidSourceBranchLimit f k).map sourceStarMatrixMap := by
  apply Subtype.ext
  change (((iidSourceBranchLimit f k : Measure (Fin k → ℝ)).map rootedStarMatrixMap).map
    (sourceMatrixReindex k)) =
      (iidSourceBranchLimit f k : Measure (Fin k → ℝ)).map sourceStarMatrixMap
  rw [Measure.map_map (continuous_sourceMatrixReindex k).measurable
    (continuous_rootedStarMatrixMap k).measurable]
  rfl

/-- Corrected M06 for the actual reverse trees, in the source indices
`0, …, k`, with `0` the root, iid uniform sampled vertices, and source branch
integrals. The diagonal is exactly zero, as approved in correction S01. -/
theorem tendsto_sourceSampledDistanceLaw_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) (k : ℕ) :
    Tendsto (fun n ↦ sourceSampledDistanceLaw x α (n + 1) k
      (hx (n + 1) (Nat.zero_lt_succ n)).1 (hx (n + 1) (Nat.zero_lt_succ n)).2)
      atTop (𝓝 ((iidSourceBranchLimit f k).map sourceStarMatrixMap)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_rootedSampledDistanceLaw_positive_horizons hx hαhalf hα1 hf hL1 h2 k)
    (continuous_sourceMatrixReindex k)
  rw [iidSourceBranchLimit_map_sourceStar] at h
  exact h

end Freezing2
