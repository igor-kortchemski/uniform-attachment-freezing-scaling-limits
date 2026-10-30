module

public import Freezing2.Probability.SampledTreeTransport
public import Freezing2.Probability.CanonicalMetricTransport
public import Freezing2.Probability.SupercriticalSourceMatrix
public import Freezing2.Probability.ReverseUniformVertex

/-!
# Exact finite sampled-matrix transport to the forward construction

The source joint reverse history and its independent uniform label vector are
first projected to the actual terminal tree with conditionally uniform samples.
The proved timestamp isomorphism then preserves every distance, including the
root, repeated sampled labels, and diagonal entries. No asymptotic assertion or
independence between different trees is used in this finite law identity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Classical ENNReal

namespace Freezing2

/-- The finite uniform law is supported on its defining finite set. -/
theorem ae_mem_uniformOfFinset {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (s : Finset A) :
    ∀ᵐ a ∂Measure.uniformOfFinset s, a ∈ s := by
  rw [ae_iff, Measure.uniformOfFinset_apply]
  simp

theorem ae_mem_uniform_vertex_vector {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (s : Finset A) (hs : s.Nonempty) (k : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s), ∀ i, v i ∈ s := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset s) :=
    uniformOfFinset_probability_of_nonempty s hs
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin k ↦ Measure.uniformOfFinset s) i).quasiMeasurePreserving.ae (ae_mem_uniformOfFinset s)

namespace TreeSampling

/-- The root chosen from companion active label zero, followed by the samples.
The source survival hypothesis ensures this label is actually present. -/
def reverseSampledVertex {k : ℕ} (q : Reverse × (Fin k → Label)) : Fin (k + 1) → Label :=
  Fin.cases (q.1.root (Sum.inl 0)) q.2

noncomputable def reverseDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : Reverse × (Fin k → Label)) : Fin (k + 1) → Fin (k + 1) → ℝ :=
  fun i j ↦ (q.1.graph.dist (reverseSampledVertex q i) (reverseSampledVertex q j) : ℝ) /
    (n : ℝ) ^ (1 - α)

theorem measurable_reverseDistanceMatrix (α : ℝ) (n k : ℕ) :
    Measurable (reverseDistanceMatrix α n k) :=
  measurable_from_prod_countable_left fun _ ↦ measurable_from_top

/-- The deterministic reverse label set identifies conditional iid sampling
with independent sampling from the source label set. -/
theorem sampledReverseLaw_eq_prod (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    sampledReverseLaw x n k = (Freezing1.Reverse.treeLaw x n).prod
      (Measure.pi (fun _ : Fin k ↦ Freezing1.uniformVertex x n)) := by
  have : IsFiniteMeasure (Freezing1.uniformVertex x n) :=
    uniformOfFinset_finite (Freezing1.vertexLabels x n)
  rw [Measure.prod_eq_of_sfinite, sampledReverseLaw]
  apply Measure.bind_congr_right
  filter_upwards [Freezing1.Reverse.treeLaw_vertices_and_root x n hn] with F hF
  simp only [reverseKernel, hF.1, Freezing1.uniformVertex]

/-- Exact metric transport for one terminal tree and one legal vector. -/
theorem distanceMatrix_canonicalSample {x : Freezing1.SignSequence} {n k : ℕ}
    {F : Stamped} (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.CanonicalOrder F) (hroot : Sum.inl 0 ∈ F.forest.vertices)
    (v : Fin k → Label) (hv : ∀ i, v i ∈ F.forest.vertices) (α : ℝ) :
    forwardDistanceMatrix α n k (canonicalSample x n k (F, v)) =
      reverseDistanceMatrix α n k (F.forest, v) := by
  have hr := F.forest.root_mem_roots hroot
  have hrV := F.forest.root_mem (Sum.inl 0) hroot
  have hzero := (ht.root_zero _ hrV).mpr hr
  have hm (i : Fin (k + 1)) :
      reverseSampledVertex (F.forest, v) i ∈ F.forest.vertices := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hrV
    · exact hv j
  have he (i : Fin (k + 1)) :
      forwardSampledVertex (canonicalSample x n k (F, v)) i =
        F.edgeTime (reverseSampledVertex (F.forest, v) i) := by
    refine Fin.cases ?_ (fun _ ↦ rfl) i
    exact hzero.symm
  funext i j
  simp only [forwardDistanceMatrix, reverseDistanceMatrix, he]
  change ((ReverseStamped.canonicalForwardState x n F).graph.dist _ _ : ℝ) / _ = _
  rw [ReverseStamped.canonicalForwardState_graph_dist hF ht ho (hm i) (hm j)]

/-- Conditional matrix laws agree before integrating over the common tree. -/
theorem map_stampedKernel_distanceMatrix {x : Freezing1.SignSequence} {n : ℕ}
    {F : Stamped} (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.CanonicalOrder F) (hroot : Sum.inl 0 ∈ F.forest.vertices)
    (α : ℝ) (k : ℕ) :
    (stampedKernel k F).map (forwardDistanceMatrix α n k ∘ canonicalSample x n k) =
      (stampedKernel k F).map (reverseDistanceMatrix α n k ∘ forgetStamps) := by
  rw [stampedKernel,
    Measure.map_map ((measurable_forwardDistanceMatrix α n k).comp
      (measurable_canonicalSample x n k)) (measurable_of_countable _),
    Measure.map_map ((measurable_reverseDistanceMatrix α n k).comp
      (measurable_forgetStamps k)) (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [ae_mem_uniform_vertex_vector F.forest.vertices ⟨_, hroot⟩ k] with v hv
  exact distanceMatrix_canonicalSample hF ht ho hroot v hv α

/-- The actual forward and reverse conditional sampled-distance laws agree. -/
theorem map_sampledForwardLaw_distanceMatrix (x : Freezing1.SignSequence) (α : ℝ) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hroot : Sum.inl 0 ∈ Freezing1.vertexLabels x n) :
    (sampledForwardLaw x n k).map (forwardDistanceMatrix α n k) =
      (sampledReverseLaw x n k).map (reverseDistanceMatrix α n k) := by
  rw [← map_sampledStampedLaw_canonicalSample x n k hn,
    ← map_sampledStampedLaw_forgetStamps x n k,
    Measure.map_map (measurable_forwardDistanceMatrix α n k) (measurable_canonicalSample x n k),
    Measure.map_map (measurable_reverseDistanceMatrix α n k) (measurable_forgetStamps k),
    sampledStampedLaw,
    Measure.map_bind measurable_from_top.aemeasurable
      ((measurable_forwardDistanceMatrix α n k).comp (measurable_canonicalSample x n k)).aemeasurable,
    Measure.map_bind measurable_from_top.aemeasurable
      ((measurable_reverseDistanceMatrix α n k).comp (measurable_forgetStamps k)).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
    Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
    ReverseStamped.treeLaw_canonicalOrder x n hn] with F hF ht ho
  have hF' : Freezing1.Reverse.ValidAt x n 0 F.forest := by
    simpa only [Nat.sub_self] using hF
  have hr : Sum.inl 0 ∈ F.forest.vertices := by
    simpa only [hF'.vertices_eq, Freezing1.Reverse.phaseLabels_zero] using hroot
  exact map_stampedKernel_distanceMatrix hF' ht ho hr α k

end TreeSampling

/-- The two finite label conventions transport the uniform law exactly. -/
theorem map_source_uniformVertex (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    (uniformVertex x n).map toCompanionLabel =
      Freezing1.uniformVertex (companionSchedule x) n := by
  rw [← map_companion_uniformVertex x hx n,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simpa only [Function.comp_def, to_fromCompanionLabel] using
    Measure.map_id' (μ := Freezing1.uniformVertex (companionSchedule x) n)

/-- Projection of the source joint history and source sample vector to the
terminal forest and companion labels. -/
def terminalSample (n k : ℕ)
    (q : ReverseHistory.History × (Fin k → VertexLabel)) :
    TreeSampling.Reverse × (Fin k → TreeSampling.Label) :=
  (ReverseHistory.forestAt n 0 q.1, fun i ↦ toCompanionLabel (q.2 i))

theorem measurable_terminalSample (n k : ℕ) : Measurable (terminalSample n k) := by
  change Measurable (Prod.map (ReverseHistory.forestAt n 0)
    (fun v : Fin k → VertexLabel ↦ fun i ↦ toCompanionLabel (v i)))
  exact (show Measurable (ReverseHistory.forestAt n 0) from measurable_pi_apply (n - 0)).prodMap
    (measurable_of_countable _)

/-- Sampling labels independently of the reverse history is exactly uniform
sampling conditional on its actual terminal finite tree. -/
theorem map_sampledReverseVectorLaw_terminalSample (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (hs : SurvivesThrough x n) (k : ℕ) :
    (sampledReverseVectorLaw x n k).map (terminalSample n k) =
      TreeSampling.sampledReverseLaw (companionSchedule x) n k := by
  have : IsProbabilityMeasure (uniformVertex x n) :=
    uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  change (Measure.map (Prod.map (ReverseHistory.forestAt n 0)
      (fun v : Fin k → VertexLabel ↦ fun i ↦ toCompanionLabel (v i)))
    ((ReverseHistory.jointLaw (companionSchedule x) n).prod
      (Measure.pi (fun _ : Fin k ↦ uniformVertex x n)))) = _
  rw [← Measure.map_prod_map _ _
    (show Measurable (ReverseHistory.forestAt n 0) from measurable_pi_apply (n - 0))
    (measurable_of_countable (fun v : Fin k → VertexLabel ↦ fun i ↦ toCompanionLabel (v i))),
    ReverseHistory.jointLaw_terminal_marginal,
    Measure.pi_map_pi (fun _ ↦ (measurable_of_countable toCompanionLabel).aemeasurable)]
  simp_rw [map_source_uniformVertex x hx n]
  exact (TreeSampling.sampledReverseLaw_eq_prod _ n k
    (companion_before_extinction x hx hs).le).symm

theorem sourceSampledVertex_eq_terminalSample {k : ℕ} (n : ℕ)
    (q : ReverseHistory.History × (Fin k → VertexLabel)) (i : Fin (k + 1)) :
    sourceSampledVertex n q i = TreeSampling.reverseSampledVertex (terminalSample n k q) i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [TreeSampling.reverseSampledVertex, terminalSample, reverseTerminalRoot, toCompanionLabel]
  · simp [TreeSampling.reverseSampledVertex, terminalSample]

/-- The source matrix law is the literal distance-matrix law of the actual
forward tree with iid uniform vertices and root zero. This is an exact finite
identity; repeated samples, the zero diagonal, and `k = 0` are all retained. -/
theorem sourceSampledDistanceLaw_eq_forwardSampledDistanceLaw
    (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : SurvivesThrough (x n) n) :
    sourceSampledDistanceLaw x α n k hx hs =
      TreeSampling.forwardSampledDistanceLaw (companionSchedule (x n)) α n k := by
  rw [sourceSampledDistanceLaw_eq_map]
  apply Subtype.ext
  change (sampledReverseVectorLaw (x n) n k).map (sourceSampledDistanceMatrix α n k) =
    (TreeSampling.sampledForwardLaw (companionSchedule (x n)) n k).map
      (TreeSampling.forwardDistanceMatrix α n k)
  have hr : Sum.inl 0 ∈ Freezing1.vertexLabels (companionSchedule (x n)) n := by
    simpa only [toCompanionLabel, Nat.sub_self] using
      toCompanionLabel_mem (x n) hx (active_one_mem_vertexLabels (x n) hs)
  rw [TreeSampling.map_sampledForwardLaw_distanceMatrix _ α n k
    (companion_before_extinction (x n) hx hs).le hr,
    ← map_sampledReverseVectorLaw_terminalSample (x n) hx hs k,
    Measure.map_map (TreeSampling.measurable_reverseDistanceMatrix α n k)
      (measurable_terminalSample n k)]
  apply Measure.map_congr
  filter_upwards [sourceSampledDistanceMatrix_eq_graphDistance (x n) hx hs α] with q hq
  funext i j
  rw [hq i j, sourceSampledVertex_eq_terminalSample n q i,
    sourceSampledVertex_eq_terminalSample n q j]
  rfl

end Freezing2
