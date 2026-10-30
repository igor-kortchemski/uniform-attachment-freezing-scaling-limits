module

public import Freezing2.Probability.RootedSampledMatrix
public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Probability.WeakPerturbation
public import Freezing2.Audit.Obstructions

/-!
# The corrected supercritical finite-dimensional limit for actual reverse trees

The root-inclusive distance law is approximated in probability by a continuous
function of the actual iid branch vector. The limiting law includes the
deterministic root branch zero and has zero diagonal. Forward-tree law transport
is a separate obligation; no equality of the two constructions is assumed here.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory

/-- Append the zero root branch to a vector of sampled branch lengths. -/
def rootAugmentedBranch {k : ℕ} (b : Fin k → ℝ) : Option (Fin k) → ℝ
  | none => 0
  | some i => b i

/-- The corrected star matrix, including the distinguished root index. -/
def rootedStarMatrixMap {k : ℕ} (b : Fin k → ℝ) : Option (Fin k) → Option (Fin k) → ℝ
  | none, none => 0
  | none, some j => b j
  | some i, none => b i
  | some i, some j => if i = j then 0 else b i + b j

theorem rootedStarMatrixMap_eq_starDistance {k : ℕ} (b : Fin k → ℝ) :
    rootedStarMatrixMap b = Audit.starDistance (rootAugmentedBranch b) := by
  funext i j
  cases i <;> cases j <;> simp [rootedStarMatrixMap, Audit.starDistance, rootAugmentedBranch]

@[simp] theorem rootedStarMatrixMap_diag {k : ℕ} (b : Fin k → ℝ) (i : Option (Fin k)) :
    rootedStarMatrixMap b i i = 0 := by
  rw [rootedStarMatrixMap_eq_starDistance]
  exact Audit.starDistance_self _ _

theorem continuous_rootedStarMatrixMap (k : ℕ) :
    Continuous (rootedStarMatrixMap (k := k)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i with
  | none => cases j <;> first | exact continuous_const | exact continuous_apply _
  | some i =>
    cases j with
    | none => exact continuous_apply i
    | some j =>
      by_cases h : i = j
      · simpa only [rootedStarMatrixMap, h, ↓reduceIte] using
          (continuous_const : Continuous (fun _ : Fin k → ℝ ↦ (0 : ℝ)))
      · simp only [rootedStarMatrixMap, h, ↓reduceIte]
        have hi : Continuous (fun b : Fin k → ℝ ↦ b i) := continuous_apply i
        have hj : Continuous (fun b : Fin k → ℝ ↦ b j) := continuous_apply j
        convert hi.add hj using 1

theorem rootedSampledStarMatrix_eq_map (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) :
    rootedSampledStarMatrix x α n k q =
      rootedStarMatrixMap (fun i ↦ normalizedBranchLength x α n (q.2 i)) := by
  funext i j
  cases i <;> cases j <;>
    simp only [rootedSampledStarMatrix, rootedStarMatrixMap, sampledStarMatrix,
      sampledBranchSum, normalizedBranchLength]

/-- The concrete history and iid-label law, packaged as a probability measure. -/
noncomputable def sampledReverseVectorProbability (x : ℕ → ℤ) (n k : ℕ)
    (hx : IsSigned x) (hs : SurvivesThrough x n) :
    ProbabilityMeasure (History × (Fin k → VertexLabel)) :=
  ⟨sampledReverseVectorLaw x n k, sampledReverseVectorLaw_probability x hx hs⟩

/-- The root-inclusive scaled distance law of the actual reverse graph. -/
noncomputable def rootedSampledDistanceLaw (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : SurvivesThrough (x n) n) :
    ProbabilityMeasure (Option (Fin k) → Option (Fin k) → ℝ) :=
  (sampledReverseVectorProbability (x n) n k hx hs).map (rootedSampledDistanceMatrix α n k)

theorem rootedSampledStarMatrix_law (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : SurvivesThrough (x n) n) :
    (sampledReverseVectorProbability (x n) n k hx hs).map (rootedSampledStarMatrix x α n k) =
      (uniformBranchVectorLaw x α n k hx (hs n le_rfl).le).map rootedStarMatrixMap := by
  let := uniformVertex_isProbabilityMeasure (x n) hx (hs n le_rfl).le
  let B : (Fin k → VertexLabel) → (Fin k → ℝ) :=
    fun v i ↦ normalizedBranchLength x α n (v i)
  have hB : Measurable B := measurable_of_countable _
  have he : rootedSampledStarMatrix x α n k = rootedStarMatrixMap ∘ B ∘ Prod.snd := by
    funext q
    exact rootedSampledStarMatrix_eq_map x α n k q
  apply Subtype.ext
  change (sampledReverseVectorLaw (x n) n k).map (rootedSampledStarMatrix x α n k) =
    ((Measure.pi (fun _ : Fin k ↦ uniformVertex (x n) n)).map B).map rootedStarMatrixMap
  rw [he, ← Function.comp_assoc,
    ← Measure.map_map ((continuous_rootedStarMatrixMap k).measurable.comp hB) measurable_snd]
  rw [sampledReverseVectorLaw, Measure.map_snd_prod, measure_univ, one_smul]
  exact (Measure.map_map (continuous_rootedStarMatrixMap k).measurable hB).symm

/-- The corrected root-inclusive M06 finite-dimensional limit for the actual
reverse tree. All iid coordinates and possible label collisions are retained. -/
theorem tendsto_rootedSampledDistanceLaw
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) (k : ℕ) :
    Tendsto (fun n ↦ rootedSampledDistanceLaw x α n k (hx n).1 (hx n).2)
      atTop (𝓝 ((iidPrimitiveLaw g k).map rootedStarMatrixMap)) := by
  have hbranch := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_uniformBranchVectorLaw hx hα1 hL1 hpos k) (continuous_rootedStarMatrixMap k)
  let μ (n : ℕ) := sampledReverseVectorProbability (x n) n k (hx n).1 (hx n).2
  apply tendsto_probabilityMap_of_error_probability μ
    (fun n ↦ measurable_rootedSampledDistanceMatrix α n k)
    (fun n ↦ measurable_rootedSampledStarMatrix x α n k)
    (fun ε hε ↦ tendsto_rootedSampledStarMatrix_error_probability hx hαhalf hα1 hL1 hpos h2 k hε)
  exact hbranch.congr' (Eventually.of_forall fun n ↦
    (rootedSampledStarMatrix_law x α n k (hx n).1 (hx n).2).symm)

/-- Source integral specialization on the paper's positive horizons. The
resulting matrix is exactly `starDistance` with root branch zero and iid
branches `∫_[0,U] 1/(2*f)`, using the approved diagonal correction. -/
theorem tendsto_rootedSampledDistanceLaw_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) (k : ℕ) :
    Tendsto (fun n ↦ rootedSampledDistanceLaw x α (n + 1) k
      (hx (n + 1) (Nat.zero_lt_succ n)).1 (hx (n + 1) (Nat.zero_lt_succ n)).2)
      atTop (𝓝 ((iidSourceBranchLimit f k).map rootedStarMatrixMap)) := by
  have h := (tendsto_rootedSampledDistanceLaw (admissible_initialRowExtension hx)
    hαhalf hα1 (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) k).comp
      (tendsto_add_atTop_nat 1)
  rw [iidPrimitiveLaw_reciprocal_eq hL1.1] at h
  apply h.congr'
  exact Eventually.of_forall fun n ↦ by
    apply Subtype.ext
    simp only [Function.comp_apply, rootedSampledDistanceLaw, sampledReverseVectorProbability,
      initialRowExtension, Nat.add_one_ne_zero, ite_false]

end Freezing2
