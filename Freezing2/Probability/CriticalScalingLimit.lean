module

public import Freezing2.Probability.CriticalDistanceLimit
public import Freezing2.Probability.CriticalTreeBridge
public import Freezing2.Probability.SampledMatrixTransport

/-!
# The critical scaling limit (Theorem `thm:critique`, M03)

The annealed sampled distance matrices of the actual scaled uniformly measured
forward trees are the sample blocks of the root-augmented reverse matrices, hence
equal the laws of the scaled reverse distances between iid uniform vertices. By the
critical `eq:GP` they converge to `criticalDistanceLaw g k`, with `g = 1/f`. The proved
forward `eq:GH` and Proposition `C.1` (for a family of block laws) then give weak
GHP convergence.

The limit `criticalTreeLaw g` is defined as the unique law of an almost surely
fully supported random compact measured space whose annealed sampled distance
matrices are `criticalDistanceLaw g k`; it depends only on `g`. The real-tree
property of the limit (U26) is a separate statement.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace Freezing2

open ReverseHistory CriticalGenealogy

/-- The sample block of a root-augmented matrix. -/
def sampleBlock (k : ℕ) (M : Fin (k + 1) → Fin (k + 1) → ℝ) : Fin k → Fin k → ℝ :=
  fun i j ↦ M i.succ j.succ

theorem continuous_sampleBlock (k : ℕ) : Continuous (sampleBlock k) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply j.succ).comp (continuous_apply i.succ)

theorem sampleBlock_sourceSampledDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) :
    sampleBlock k (sourceSampledDistanceMatrix α n k q) = sampledDistanceMatrix α n k q := by
  funext i j
  simp [sampleBlock, sourceSampledDistanceMatrix, sourceMatrixReindex, finSuccEquiv_succ,
    rootedSampledDistanceMatrix]

theorem sampleBlock_forwardDistanceMatrix (n k : ℕ)
    (q : TreeSampling.Forward × (Fin k → ℕ)) :
    sampleBlock k (TreeSampling.forwardDistanceMatrix (1 / 2) n k q) =
      fun i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / Real.sqrt n := by
  funext i j
  simp only [sampleBlock, TreeSampling.forwardDistanceMatrix, TreeSampling.forwardSampledVertex,
    Fin.cases_succ, Real.sqrt_eq_rpow]
  norm_num

/-- **Forward annealed blocks are reverse sampled distance laws.** -/
theorem annealedDistanceLaw_forward_eq_reverse {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    MeasuredGHSpace.annealedDistanceLaw (forwardMeasuredTreeLaw xa (1 / 2) n) k =
      (samplePM hx k n).map (sampledDistanceMatrix (1 / 2) n k) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [annealedDistanceLaw_forwardMeasuredTreeLaw xa hn k]
  have hE := sourceSampledDistanceLaw_eq_forwardSampledDistanceLaw xa (1 / 2) n k (hx n).1 (hx n).2
  rw [sourceSampledDistanceLaw_eq_map] at hE
  have hE' : (sampledReverseVectorLaw (xa n) n k).map (sourceSampledDistanceMatrix (1 / 2) n k) =
      (TreeSampling.sampledForwardLaw (companionSchedule (xa n)) n k).map
        (TreeSampling.forwardDistanceMatrix (1 / 2) n k) :=
    congrArg ProbabilityMeasure.toMeasure hE
  have hB := congrArg (Measure.map (sampleBlock k)) hE'
  have hsrc : Measurable (sourceSampledDistanceMatrix (1 / 2) n k) :=
    (continuous_sourceMatrixReindex k).measurable.comp
      (measurable_rootedSampledDistanceMatrix (1 / 2) n k)
  rw [Measure.map_map (continuous_sampleBlock k).measurable hsrc,
    Measure.map_map (continuous_sampleBlock k).measurable
      (TreeSampling.measurable_forwardDistanceMatrix (1 / 2) n k)] at hB
  have h1 : sampleBlock k ∘ sourceSampledDistanceMatrix (1 / 2) n k =
      sampledDistanceMatrix (1 / 2) n k :=
    funext (sampleBlock_sourceSampledDistanceMatrix (1 / 2) n k)
  have h2 : sampleBlock k ∘ TreeSampling.forwardDistanceMatrix (1 / 2) n k =
      fun q i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / Real.sqrt n :=
    funext (sampleBlock_forwardDistanceMatrix n k)
  rw [h1, h2] at hB
  rw [← hB]
  rfl

/-- The law of the critical limit `𝒯(f)` for the reciprocal profile `g = 1/f`: the
unique law of an almost surely fully supported random compact measured space whose
annealed sampled distance matrices are `criticalDistanceLaw g k`. -/
noncomputable def criticalTreeLaw (g : ℝ → ℝ) : ProbabilityMeasure MeasuredGHSpace.{0} :=
  haveI : Nonempty (ProbabilityMeasure MeasuredGHSpace.{0}) :=
    ⟨forwardMeasuredTreeLaw (fun _ _ ↦ 1) (1 / 2) 0⟩
  Classical.epsilon fun Q ↦
    (∀ k, MeasuredGHSpace.annealedDistanceLaw Q k = criticalDistanceLaw g k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), MeasuredGHSpace.HasFullSupport X

theorem forwardMeasuredTreeLaw_congr {x x' : ℕ → ℕ → ℤ} {n : ℕ} (h : x n = x' n) (α : ℝ) :
    forwardMeasuredTreeLaw x α n = forwardMeasuredTreeLaw x' α n := by
  simp only [forwardMeasuredTreeLaw, freezingTreeLaw, h]

/-- **`eq:GP`** for the actual forward trees: the annealed sampled distance matrices
of `forwardMeasuredTreeLaw x (1/2) n` converge to `criticalDistanceLaw (1/f) k`. -/
theorem tendsto_forward_annealedDistanceLaw_critical {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t)) (k : ℕ) :
    Tendsto (fun n ↦ MeasuredGHSpace.annealedDistanceLaw (forwardMeasuredTreeLaw x (1 / 2) n) k)
      atTop (𝓝 (criticalDistanceLaw (fun t ↦ 1 / f t) k)) := by
  have hxa := admissible_initialRowExtension hx
  have hrev := tendsto_sampledDistanceLaw_critical hxa
    (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)
    (hasLocalSquareMomentProfile_initialRowExtension h2) k
  apply hrev.congr'
  filter_upwards [initialRowExtension_eventually_eq x, eventually_gt_atTop 0] with n hn hn0
  rw [forwardMeasuredTreeLaw_congr hn.symm, annealedDistanceLaw_forward_eq_reverse hxa hn0 k]

/-- **Theorem `thm:critique` (M03), up to the real-tree property.** Under the source
hypotheses `Lim_{1/f}`, `Lim_{1/f²}` and `max S = O(√n)`, the actual scaled uniformly
measured forward trees converge in distribution, for the Gromov–Hausdorff–Prokhorov
topology, to `criticalTreeLaw (1/f)`, a law depending only on `f`; the limit has
almost surely full support and annealed sampled distance matrices
`criticalDistanceLaw (1/f) k`. -/
theorem critical_scaling_limit {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    Tendsto (forwardMeasuredTreeLaw x (1 / 2)) atTop
        (𝓝 (criticalTreeLaw (fun t ↦ 1 / f t))) ∧
      (∀ k, MeasuredGHSpace.annealedDistanceLaw (criticalTreeLaw (fun t ↦ 1 / f t)) k =
        criticalDistanceLaw (fun t ↦ 1 / f t) k) ∧
      ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
        MeasuredGHSpace.HasFullSupport X := by
  obtain ⟨Q, hQ, hQL, hQS⟩ := MeasuredGHSpace.leafTightFamily _ _
    (tendsto_forward_annealedDistanceLaw_critical hx hf hL1 h2)
    (fun _ hδ ↦ forwardMeasuredTreeLaw_leafTight hx hf hL1 hpop hδ)
  have hspec := Classical.epsilon_spec (p := fun Q : ProbabilityMeasure MeasuredGHSpace.{0} ↦
    (∀ k, MeasuredGHSpace.annealedDistanceLaw Q k = criticalDistanceLaw (fun t ↦ 1 / f t) k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), MeasuredGHSpace.HasFullSupport X) ⟨Q, hQL, hQS⟩
  have heq : criticalTreeLaw (fun t ↦ 1 / f t) = Q :=
    MeasuredGHSpace.eq_of_annealedDistanceLaw_eq _ _
      (fun k ↦ (hspec.1 k).trans (hQL k).symm) hspec.2 hQS
  rw [heq]
  exact ⟨hQ, hQL, hQS⟩

end Freezing2
