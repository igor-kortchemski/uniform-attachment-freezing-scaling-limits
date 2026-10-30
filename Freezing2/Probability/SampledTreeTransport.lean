module

public import Freezing2.Probability.SourceSameLaw
public import Freezing2.Probability.UniformTransport
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Equality of actual tree laws with iid uniform vertex samples

The sample vector is drawn conditionally and uniformly from the actual finite
vertex set of one common tree. Canonical timestamp transport carries the whole
sampled object to the forward law, while forgetting timestamps recovers the
plain reverse law. Repeated sampled vertices and a zero-length vector remain.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Classical ENNReal

namespace Freezing2.TreeSampling

abbrev Label := ℕ ⊕ ℕ
abbrev Stamped := Freezing1.ReverseStamped.Forest
abbrev Reverse := Freezing1.Reverse.Forest
abbrev Forward := Freezing1.Forward.State

noncomputable def stampedKernel (k : ℕ) (F : Stamped) : Measure (Stamped × (Fin k → Label)) :=
  (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset F.forest.vertices)).map (fun v ↦ (F, v))

noncomputable def reverseKernel (k : ℕ) (F : Reverse) : Measure (Reverse × (Fin k → Label)) :=
  (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset F.vertices)).map (fun v ↦ (F, v))

noncomputable def forwardKernel (k : ℕ) (s : Forward) : Measure (Forward × (Fin k → ℕ)) :=
  (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s.vertices)).map (fun v ↦ (s, v))

noncomputable def sampledStampedLaw (x : Freezing1.SignSequence) (n k : ℕ) :
    Measure (Stamped × (Fin k → Label)) :=
  (Freezing1.ReverseStamped.treeLaw x n).bind (stampedKernel k)

noncomputable def sampledReverseLaw (x : Freezing1.SignSequence) (n k : ℕ) :
    Measure (Reverse × (Fin k → Label)) :=
  (Freezing1.Reverse.treeLaw x n).bind (reverseKernel k)

noncomputable def sampledForwardLaw (x : Freezing1.SignSequence) (n k : ℕ) :
    Measure (Forward × (Fin k → ℕ)) :=
  (Freezing1.Forward.treeLaw x n).bind (forwardKernel k)

theorem forwardKernel_probability {m : ℕ} {s : Forward}
    (hs : Freezing1.Forward.ValidAt m s) (k : ℕ) : IsProbabilityMeasure (forwardKernel k s) := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) :=
    uniformOfFinset_probability_of_nonempty s.vertices ⟨0, hs.root_mem⟩
  unfold forwardKernel
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

instance sampledForwardLaw_probability (x : Freezing1.SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (sampledForwardLaw x n k) := by
  unfold sampledForwardLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Freezing1.Forward.treeLaw_valid x n] with s hs
  exact forwardKernel_probability hs k

/-- Root zero followed by the `k` actual uniform forward samples. -/
def forwardSampledVertex {k : ℕ} (q : Forward × (Fin k → ℕ)) : Fin (k + 1) → ℕ :=
  Fin.cases 0 q.2

/-- The literal source normalization and root-inclusive finite matrix. -/
noncomputable def forwardDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : Forward × (Fin k → ℕ)) : Fin (k + 1) → Fin (k + 1) → ℝ :=
  fun i j ↦ (q.1.graph.dist (forwardSampledVertex q i) (forwardSampledVertex q j) : ℝ) /
    (n : ℝ) ^ (1 - α)

theorem measurable_forwardDistanceMatrix (α : ℝ) (n k : ℕ) :
    Measurable (forwardDistanceMatrix α n k) :=
  measurable_from_prod_countable_left fun _ ↦ measurable_from_top

/-- The actual forward sampled-distance law, with the root at index zero. -/
noncomputable def forwardSampledDistanceLaw (x : Freezing1.SignSequence) (α : ℝ) (n k : ℕ) :
    ProbabilityMeasure (Fin (k + 1) → Fin (k + 1) → ℝ) :=
  ProbabilityMeasure.map
    (⟨sampledForwardLaw x n k, sampledForwardLaw_probability x n k⟩ :
      ProbabilityMeasure (Forward × (Fin k → ℕ))) (forwardDistanceMatrix α n k)

def forgetStamps {k : ℕ} (q : Stamped × (Fin k → Label)) : Reverse × (Fin k → Label) :=
  (q.1.forest, q.2)

noncomputable def canonicalSample (x : Freezing1.SignSequence) (n k : ℕ)
    (q : Stamped × (Fin k → Label)) : Forward × (Fin k → ℕ) :=
  (ReverseStamped.canonicalForwardState x n q.1, fun i ↦ q.1.edgeTime (q.2 i))

theorem measurable_forgetStamps (k : ℕ) : Measurable (@forgetStamps k) :=
  measurable_from_prod_countable_left fun _ ↦ measurable_from_top

theorem measurable_canonicalSample (x : Freezing1.SignSequence) (n k : ℕ) :
    Measurable (canonicalSample x n k) :=
  measurable_from_prod_countable_left fun _ ↦ measurable_from_top

theorem map_stampedKernel_forgetStamps (k : ℕ) (F : Stamped) :
    (stampedKernel k F).map forgetStamps = reverseKernel k F.forest := by
  rw [stampedKernel, Measure.map_map (measurable_forgetStamps k) (measurable_of_countable _)]
  rfl

/-- Sampling is unchanged when the auxiliary edge timestamps are forgotten. -/
theorem map_sampledStampedLaw_forgetStamps (x : Freezing1.SignSequence) (n k : ℕ) :
    (sampledStampedLaw x n k).map forgetStamps = sampledReverseLaw x n k := by
  rw [sampledStampedLaw, Measure.map_bind measurable_from_top.aemeasurable
    (measurable_forgetStamps k).aemeasurable]
  simp_rw [map_stampedKernel_forgetStamps]
  rw [← Measure.bind_map (m := Freezing1.ReverseStamped.treeLaw x n)
    (f := Freezing1.ReverseStamped.Forest.forest) (g := reverseKernel k)
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  rw [Freezing1.ReverseStamped.map_treeLaw]
  rfl

theorem map_stampedKernel_canonicalSample {x : Freezing1.SignSequence} {n : ℕ}
    {F : Stamped} (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.CanonicalOrder F) (k : ℕ) :
    (stampedKernel k F).map (canonicalSample x n k) =
      forwardKernel k (ReverseStamped.canonicalForwardState x n F) := by
  rw [stampedKernel, Measure.map_map (measurable_canonicalSample x n k) (measurable_of_countable _)]
  calc
    _ = ((Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset F.forest.vertices)).map
        (fun v i ↦ F.edgeTime (v i))).map
          (fun v ↦ (ReverseStamped.canonicalForwardState x n F, v)) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by
      rw [ReverseStamped.map_uniform_vertex_vector hF ht ho]
      rfl

/-- N01 extends to one common actual tree with any finite iid uniform sample
vector, using the proved conditional uniform transport rather than a postulated coupling. -/
theorem map_sampledStampedLaw_canonicalSample (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (sampledStampedLaw x n k).map (canonicalSample x n k) = sampledForwardLaw x n k := by
  rw [sampledStampedLaw, Measure.map_bind measurable_from_top.aemeasurable
    (measurable_canonicalSample x n k).aemeasurable]
  calc
    _ = (Freezing1.ReverseStamped.treeLaw x n).bind
        (fun F ↦ forwardKernel k (ReverseStamped.canonicalForwardState x n F)) := by
      apply Measure.bind_congr_right
      filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
        Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
        ReverseStamped.treeLaw_canonicalOrder x n hn] with F hF ht ho
      exact map_stampedKernel_canonicalSample (by simpa only [Nat.sub_self] using hF) ht ho k
    _ = ((Freezing1.ReverseStamped.treeLaw x n).map (ReverseStamped.canonicalForwardState x n)).bind
        (forwardKernel k) :=
      (Measure.bind_map (m := Freezing1.ReverseStamped.treeLaw x n)
        (f := ReverseStamped.canonicalForwardState x n) (g := forwardKernel k)
        measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
    _ = _ := by rw [ReverseStamped.forward_reverse_same_law x n hn]; rfl

end Freezing2.TreeSampling
