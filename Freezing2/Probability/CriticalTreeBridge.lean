module

public import Freezing2.Probability.SampledReconstruction
public import Freezing2.Probability.ForwardLeafTightness
public import Freezing2.MainResults.SubcriticalDistribution

/-!
# The critical forward trees as random measured spaces

The scaled uniformly measured forward trees `forwardMeasuredTreeLaw x (1/2) n`
are random compact measured spaces. Their annealed covering-radius tails are
exactly the probabilities of the leaf-tightness event for the forward tree
with conditionally iid uniform vertices, so `eq:GH` is the leaf-tightness
hypothesis of Proposition `C.1`. Consequently Theorem `thm:critique` reduces to
the convergence of the annealed sampled distance matrices, `eq:GP`.
-/

@[expose] public section

open Filter MeasureTheory Set Metric Topology
open scoped ENNReal

namespace Freezing2

/-- For a finite sample of a compact space, the Hausdorff distance to the whole
space exceeds `δ` exactly when some point is farther than `δ` from every sample. -/
theorem lt_hausdorffDist_univ_range_iff {X : Type*} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {k : ℕ} (v : Fin (k + 1) → X) (δ : ℝ) :
    δ < hausdorffDist (univ : Set X) (range v) ↔ ∃ y, ∀ i, δ < dist y (v i) := by
  have hfin : hausdorffEDist (univ : Set X) (range v) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded univ_nonempty (range_nonempty v)
      isBounded_of_compactSpace (finite_range v).isCompact.isBounded
  constructor
  · intro h
    by_contra hno
    push Not at hno
    rcases lt_or_ge δ 0 with hδ | hδ
    · obtain ⟨i, hi⟩ := hno (v 0)
      exact absurd (hδ.trans_le dist_nonneg) (not_lt.mpr hi)
    · refine (not_lt.mpr ?_) h
      apply hausdorffDist_le_of_mem_dist hδ
      · intro y _
        obtain ⟨i, hi⟩ := hno y
        exact ⟨v i, mem_range_self i, hi⟩
      · rintro _ ⟨i, rfl⟩
        exact ⟨v i, mem_univ _, by rw [dist_self]; exact hδ⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, ⟨i, rfl⟩, hz⟩ := (finite_range v).isCompact.exists_infDist_eq_dist
      (range_nonempty v) y
    exact (hz ▸ hy i).trans_le (infDist_le_hausdorffDist_of_mem (mem_univ y) hfin)

theorem sampleCoverRadiusOn_fullCarrier {X : Type*} [MetricSpace X] [CompactSpace X]
    [Nonempty X] (k : ℕ) (v : Fin (k + 1) → X) :
    sampleCoverRadiusOn (fullCarrierCompact X) k v = hausdorffDist (univ : Set X) (range v) := by
  rw [sampleCoverRadiusOn, TopologicalSpace.NonemptyCompacts.dist_eq]
  rfl

/-- Uniform iid samples of the forward vertex subtype, read as labels, are
uniform iid samples of the forward vertex labels. -/
theorem map_pi_forwardVertexMeasure (s : Freezing1.Forward.State) (k : ℕ)
    (hne : s.vertices.Nonempty) :
    (Measure.pi (fun _ : Fin k ↦ forwardVertexMeasure s)).map
        (fun w : Fin k → {v // v ∈ s.vertices} ↦ fun i ↦ (w i : ℕ)) =
      Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s.vertices) := by
  classical
  have : IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) :=
    uniformOfFinset_probability_of_nonempty _ hne
  have hmap : (forwardVertexMeasure s).map (Subtype.val : {v // v ∈ s.vertices} → ℕ) =
      Measure.uniformOfFinset s.vertices := map_uniform_vertex_subtype_val s.vertices
  have : ∀ _ : Fin k, SigmaFinite ((forwardVertexMeasure s).map
      (Subtype.val : {v // v ∈ s.vertices} → ℕ)) := fun _ ↦ by rw [hmap]; infer_instance
  rw [Measure.pi_map_pi (hμ := this) (fun _ ↦ measurable_subtype_coe.aemeasurable)]
  simp_rw [hmap]

/-- The covering-radius tail of a scaled forward tree is the probability that
some vertex is farther than `δ` from all `k + 1` uniform vertex labels. -/
theorem forward_iidCoverRadiusLaw_Ioi {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {c : ℝ} (hc : 0 < c) (k : ℕ) (δ : ℝ) :
    (iidCoverRadiusLaw (forwardMeasuredSpace c s) k : Measure ℝ) (Ioi δ) =
      Measure.pi (fun _ : Fin (k + 1) ↦ Measure.uniformOfFinset s.vertices)
        {v | ∃ y ∈ s.vertices, ∀ i, δ < c * (s.graph.dist y (v i) : ℝ)} := by
  classical
  have hconn := hs.tree_connected
  rw [forwardMeasuredSpace, dite_eq_left (show s.tree.Connected ∧ 0 < c from ⟨hconn, hc⟩),
    CompactMeasuredSpace.iidCoverRadiusLaw_apply _ k measurableSet_Ioi]
  let := scaledGraphMetric s.tree hconn c hc
  let := hconn.nonempty
  have hne : s.vertices.Nonempty := ⟨0, hs.root_mem⟩
  have hE : MeasurableSet {v : Fin (k + 1) → ℕ |
      ∃ y ∈ s.vertices, ∀ i, δ < c * (s.graph.dist y (v i) : ℝ)} :=
    (Set.to_countable _).measurableSet
  rw [← map_pi_forwardVertexMeasure s (k + 1) hne,
    Measure.map_apply (f := fun w : Fin (k + 1) → {v // v ∈ s.vertices} ↦ fun i ↦ (w i : ℕ))
      (measurable_pi_iff.mpr fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i)) hE]
  congr 1
  ext w
  simp only [mem_preimage, mem_Ioi]
  rw [sampleCoverRadiusOn_fullCarrier, lt_hausdorffDist_univ_range_iff]
  let w' : Fin (k + 1) → {v // v ∈ s.vertices} := w
  constructor
  · rintro ⟨y, hy⟩
    let y' : {v // v ∈ s.vertices} := y
    refine ⟨y'.val, y'.2, fun i ↦ ?_⟩
    have h := hy i
    change δ < c * (s.tree.dist y' (w' i) : ℝ) at h
    rw [forward_tree_dist_eq hs] at h
    exact h
  · rintro ⟨y, hy, hdist⟩
    let y' : {v // v ∈ s.vertices} := ⟨y, hy⟩
    refine ⟨y', fun i ↦ ?_⟩
    change δ < c * (s.tree.dist y' (w' i) : ℝ)
    rw [forward_tree_dist_eq hs]
    exact hdist i

theorem one_div_rpow_half_mul (n : ℕ) (d : ℝ) :
    1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ)) * d = d / Real.sqrt n := by
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

/-- The annealed covering-radius tail of the critical forward measured trees is
the probability of the forward leaf-tightness event with `k + 1` samples. -/
theorem annealedCoverRadiusLaw_forwardMeasuredTreeLaw (x : ℕ → ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    (k : ℕ) (δ : ℝ) :
    (MeasuredGHSpace.annealedCoverRadiusLaw (forwardMeasuredTreeLaw x (1 / 2) n) k :
      Measure ℝ) (Ioi δ) =
      TreeSampling.sampledForwardLaw (companionSchedule (x n)) n (k + 1)
        {q | ∃ v ∈ q.1.vertices, ∀ i, δ < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n} := by
  have hc : 0 < 1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hE : MeasurableSet {q : TreeSampling.Forward × (Fin (k + 1) → ℕ) |
      ∃ v ∈ q.1.vertices, ∀ i, δ < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n} :=
    (measurable_from_prod_countable_left fun _ ↦ measurable_from_top :
      Measurable (fun q : TreeSampling.Forward × (Fin (k + 1) → ℕ) ↦
        ∃ v ∈ q.1.vertices, ∀ i, δ < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n)).setOf
  rw [MeasuredGHSpace.annealedCoverRadiusLaw, continuousMixture_apply _ _ measurableSet_Ioi]
  change ∫⁻ X, _ ∂((freezingTreeLaw x n).map (fun s ↦ toMeasuredGHSpace
    (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ))) s))) = _
  rw [lintegral_map (MeasuredGHSpace.measurable_sampledCoverRadiusLaw_apply k measurableSet_Ioi)
      measurable_from_top,
    TreeSampling.sampledForwardLaw, Measure.bind_apply hE measurable_from_top.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Freezing1.Forward.treeLaw_valid (companionSchedule (x n)) n] with s hs
  change (iidCoverRadiusLaw (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ))) s) k :
    Measure ℝ) (Ioi δ) = _
  rw [forward_iidCoverRadiusLaw_Ioi hs hc, TreeSampling.forwardKernel,
    Measure.map_apply (measurable_of_countable _) hE]
  congr 1
  ext v
  simp only [mem_ofPred_eq, mem_preimage, one_div_rpow_half_mul]

/-- Forward leaf-tightness is the leaf-tightness hypothesis of `C.1` for the
critical forward measured trees. -/
theorem forwardMeasuredTreeLaw_leafTight {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (MeasuredGHSpace.annealedCoverRadiusLaw (forwardMeasuredTreeLaw x (1 / 2) n) k :
        Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 1).mpr (forward_critical_leaf_tightness hx hf hL1 hpop hδ)
  refine h.congr' (Eventually.of_forall fun k ↦ limsup_congr ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (annealedCoverRadiusLaw_forwardMeasuredTreeLaw x hn k δ).symm

/-- The sampled distance law of a scaled forward tree is the law of scaled
graph distances between iid uniform vertex labels. -/
theorem forward_iidDistanceLaw_apply {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {c : ℝ} (hc : 0 < c) (k : ℕ)
    {E : Set (Fin k → Fin k → ℝ)} (hE : MeasurableSet E) :
    (iidDistanceLaw (forwardMeasuredSpace c s) k : Measure (Fin k → Fin k → ℝ)) E =
      Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset s.vertices)
        {v | (fun i j ↦ c * (s.graph.dist (v i) (v j) : ℝ)) ∈ E} := by
  classical
  have hconn := hs.tree_connected
  rw [forwardMeasuredSpace, dite_eq_left (show s.tree.Connected ∧ 0 < c from ⟨hconn, hc⟩),
    CompactMeasuredSpace.iidDistanceLaw_apply _ k hE]
  let := scaledGraphMetric s.tree hconn c hc
  have hne : s.vertices.Nonempty := ⟨0, hs.root_mem⟩
  have hE' : MeasurableSet {v : Fin k → ℕ | (fun i j ↦ c * (s.graph.dist (v i) (v j) : ℝ)) ∈ E} :=
    (Set.to_countable _).measurableSet
  rw [← map_pi_forwardVertexMeasure s k hne,
    Measure.map_apply (f := fun w : Fin k → {v // v ∈ s.vertices} ↦ fun i ↦ (w i : ℕ))
      (measurable_pi_iff.mpr fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i)) hE']
  congr 1
  ext w
  let w' : Fin k → {v // v ∈ s.vertices} := w
  have hd : distanceMatrix k w = fun i j ↦ c * (s.graph.dist (w' i).val (w' j).val : ℝ) := by
    funext i j
    change c * (s.tree.dist (w' i) (w' j) : ℝ) = _
    rw [forward_tree_dist_eq hs]
  simp only [mem_preimage]
  rw [hd]
  rfl

/-- The annealed matrices of the critical forward measured trees are the laws
of the scaled graph distances between iid uniform vertices. -/
theorem annealedDistanceLaw_forwardMeasuredTreeLaw (x : ℕ → ℕ → ℤ) {n : ℕ} (hn : 0 < n)
    (k : ℕ) :
    (MeasuredGHSpace.annealedDistanceLaw (forwardMeasuredTreeLaw x (1 / 2) n) k :
      Measure (Fin k → Fin k → ℝ)) =
      (TreeSampling.sampledForwardLaw (companionSchedule (x n)) n k).map
        (fun q i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / Real.sqrt n) := by
  have hc : 0 < 1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hg : Measurable (fun q : TreeSampling.Forward × (Fin k → ℕ) ↦
      fun i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / Real.sqrt n) :=
    measurable_from_prod_countable_left fun _ ↦ measurable_from_top
  ext E hE
  rw [MeasuredGHSpace.annealedDistanceLaw, continuousMixture_apply _ _ hE]
  change ∫⁻ X, _ ∂((freezingTreeLaw x n).map (fun s ↦ toMeasuredGHSpace
    (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ))) s))) = _
  rw [lintegral_map (MeasuredGHSpace.measurable_sampledDistanceLaw_apply k hE)
      measurable_from_top, Measure.map_apply hg hE,
    TreeSampling.sampledForwardLaw, Measure.bind_apply (hg hE) measurable_from_top.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Freezing1.Forward.treeLaw_valid (companionSchedule (x n)) n] with s hs
  change (iidDistanceLaw (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ))) s) k :
    Measure (Fin k → Fin k → ℝ)) E = _
  rw [forward_iidDistanceLaw_apply hs hc k hE, TreeSampling.forwardKernel,
    Measure.map_apply (measurable_of_countable _) (hg hE)]
  congr 1
  ext v
  simp only [mem_ofPred_eq, mem_preimage, one_div_rpow_half_mul]

/-- **Theorem `thm:critique`, reduced to `eq:GP`.** If the annealed sampled
distance matrices of the critical forward measured trees converge to the block
laws of `M`, then the trees converge in distribution for the GHP topology to a
random compact measured space whose sampled matrices have law `M` and whose
measure has full support almost surely. -/
theorem critical_scaling_limit_of_matrix_convergence {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n))
    {M : ProbabilityMeasure (ℕ → ℕ → ℝ)}
    (hGP : ∀ k : ℕ, Tendsto (fun n ↦ MeasuredGHSpace.annealedDistanceLaw
      (forwardMeasuredTreeLaw x (1 / 2) n) k) atTop (𝓝 (MeasuredGHSpace.matrixBlockLaw M k))) :
    ∃ Q : ProbabilityMeasure MeasuredGHSpace.{0},
      Tendsto (forwardMeasuredTreeLaw x (1 / 2)) atTop (𝓝 Q) ∧
      (∀ k : ℕ, MeasuredGHSpace.annealedDistanceLaw Q k = MeasuredGHSpace.matrixBlockLaw M k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), MeasuredGHSpace.HasFullSupport X :=
  MeasuredGHSpace.leafTightCriterion _ M hGP fun _ hδ ↦
    forwardMeasuredTreeLaw_leafTight hx hf hL1 hpop hδ

end Freezing2
