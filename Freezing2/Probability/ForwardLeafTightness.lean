module

public import Freezing2.Probability.CriticalGraphNet
public import Freezing2.Probability.SampledMatrixTransport

/-!
# Leaf-tightness for the actual forward tree

The source states leaf-tightness `eq:GH` for the tree `𝒯ⁿ` with conditionally
iid uniform vertices. The probability of the leaf-tightness event is a
function of the tree as a graph together with its sampled vertices, and the
event quantifies over every vertex. The proved forward/reverse law equality
N01, with the canonical timestamp isomorphism (which maps the whole reverse
vertex set onto the forward vertex set and preserves graph distance), carries
the reverse-construction theorem to the forward tree.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal

namespace Freezing2

namespace TreeSampling

/-- Some vertex of the forward tree is farther than `ε √n` from every sample. -/
def forwardLeafEvent (n k : ℕ) (ε : ℝ) : Set (Forward × (Fin k → ℕ)) :=
  {q | ∃ v ∈ q.1.vertices, ∀ i, ε < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n}

/-- The same event for the terminal reverse forest. -/
def reverseLeafEvent (n k : ℕ) (ε : ℝ) : Set (Reverse × (Fin k → Label)) :=
  {q | ∃ v ∈ q.1.vertices, ∀ i, ε < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n}

theorem measurableSet_forwardLeafEvent (n k : ℕ) (ε : ℝ) :
    MeasurableSet (forwardLeafEvent n k ε) :=
  (measurable_from_prod_countable_left fun _ ↦ measurable_from_top :
    Measurable (fun q : Forward × (Fin k → ℕ) ↦ q ∈ forwardLeafEvent n k ε)).setOf

theorem measurableSet_reverseLeafEvent (n k : ℕ) (ε : ℝ) :
    MeasurableSet (reverseLeafEvent n k ε) :=
  (measurable_from_prod_countable_left fun _ ↦ measurable_from_top :
    Measurable (fun q : Reverse × (Fin k → Label) ↦ q ∈ reverseLeafEvent n k ε)).setOf

/-- The canonical isomorphism identifies the two events for one legal sample. -/
theorem canonicalSample_mem_forwardLeafEvent_iff {x : Freezing1.SignSequence} {n k : ℕ}
    {F : Stamped} (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (ho : ReverseStamped.CanonicalOrder F) {v : Fin k → Label}
    (hv : ∀ i, v i ∈ F.forest.vertices) (ε : ℝ) :
    canonicalSample x n k (F, v) ∈ forwardLeafEvent n k ε ↔
      (F.forest, v) ∈ reverseLeafEvent n k ε := by
  change (∃ y ∈ (ReverseStamped.canonicalForwardState x n F).vertices, ∀ i, ε <
      ((ReverseStamped.canonicalForwardState x n F).graph.dist y (F.edgeTime (v i)) : ℝ) /
        Real.sqrt n) ↔
    ∃ w ∈ F.forest.vertices, ∀ i, ε < (F.forest.graph.dist w (v i) : ℝ) / Real.sqrt n
  rw [ReverseStamped.canonicalForwardState_vertices hF ht ho]
  constructor
  · rintro ⟨y, hy, hfar⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨w, hw, fun i ↦ ?_⟩
    have h := hfar i
    rwa [ReverseStamped.canonicalForwardState_graph_dist hF ht ho hw (hv i)] at h
  · rintro ⟨w, hw, hfar⟩
    refine ⟨F.edgeTime w, Finset.mem_image_of_mem _ hw, fun i ↦ ?_⟩
    rw [ReverseStamped.canonicalForwardState_graph_dist hF ht ho hw (hv i)]
    exact hfar i

/-- N01 transports the leaf-tightness event exactly. -/
theorem sampledForwardLaw_leafEvent (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hroot : Sum.inl 0 ∈ Freezing1.vertexLabels x n) (ε : ℝ) :
    sampledForwardLaw x n k (forwardLeafEvent n k ε) =
      sampledReverseLaw x n k (reverseLeafEvent n k ε) := by
  have hmf := measurableSet_forwardLeafEvent n k ε
  have hmr := measurableSet_reverseLeafEvent n k ε
  rw [← map_sampledStampedLaw_canonicalSample x n k hn, ← map_sampledStampedLaw_forgetStamps x n k,
    Measure.map_apply (measurable_canonicalSample x n k) hmf,
    Measure.map_apply (measurable_forgetStamps k) hmr, sampledStampedLaw,
    Measure.bind_apply (hmf.preimage (measurable_canonicalSample x n k))
      measurable_from_top.aemeasurable,
    Measure.bind_apply (hmr.preimage (measurable_forgetStamps k))
      measurable_from_top.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
    Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
    ReverseStamped.treeLaw_canonicalOrder x n hn] with F hF ht ho
  have hF' : Freezing1.Reverse.ValidAt x n 0 F.forest := by
    simpa only [Nat.sub_self] using hF
  have hr : Sum.inl 0 ∈ F.forest.vertices := by
    simpa only [hF'.vertices_eq, Freezing1.Reverse.phaseLabels_zero] using hroot
  rw [stampedKernel,
    Measure.map_apply (measurable_of_countable _)
      (hmf.preimage (measurable_canonicalSample x n k)),
    Measure.map_apply (measurable_of_countable _) (hmr.preimage (measurable_forgetStamps k))]
  apply measure_congr
  filter_upwards [ae_mem_uniform_vertex_vector F.forest.vertices ⟨_, hr⟩ k] with v hv
  exact propext (canonicalSample_mem_forwardLeafEvent_iff hF' ht ho hv ε)

end TreeSampling

/-- The source leaf-tightness event for the reverse history equals, almost
surely, the terminal-forest event in companion labels. -/
theorem sampledReverseVectorLaw_leafEvent (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (k : ℕ) (ε : ℝ) :
    ((ReverseHistory.jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n k))
      {q | ∃ v ∈ vertexLabels x n, ∀ i,
        ε < reverseDistance n v (q.2 i) q.1 / Real.sqrt n} =
      TreeSampling.sampledReverseLaw (companionSchedule x) n k
        (TreeSampling.reverseLeafEvent n k ε) := by
  have hext := (companion_before_extinction x hx hs).le
  have := uniformVertexVectorLaw_probability x hx (k := k) (hs n le_rfl).le
  have hvert : ∀ᵐ ω ∂ReverseHistory.jointLaw (companionSchedule x) n,
      (ReverseHistory.forestAt n 0 ω).vertices =
        Freezing1.vertexLabels (companionSchedule x) n := by
    have h := Freezing1.Reverse.treeLaw_vertices_and_root (companionSchedule x) n hext
    rw [← ReverseHistory.jointLaw_terminal_marginal x n] at h
    exact (ae_of_ae_map (show Measurable (ReverseHistory.forestAt n 0) from
      measurable_pi_apply (n - 0)).aemeasurable h).mono fun _ h ↦ h.1
  rw [← map_sampledReverseVectorLaw_terminalSample x hx hs k,
    Measure.map_apply (measurable_terminalSample n k)
      (TreeSampling.measurableSet_reverseLeafEvent n k ε)]
  apply measure_congr
  filter_upwards [(measurePreserving_fst (μ := ReverseHistory.jointLaw (companionSchedule x) n)
    (ν := uniformVertexVectorLaw x n k)).quasiMeasurePreserving.ae hvert] with q hq
  apply propext
  change (∃ v ∈ vertexLabels x n, ∀ i, ε < reverseDistance n v (q.2 i) q.1 / Real.sqrt n) ↔
    ∃ w ∈ (ReverseHistory.forestAt n 0 q.1).vertices, ∀ i,
      ε < ((ReverseHistory.forestAt n 0 q.1).graph.dist w (toCompanionLabel (q.2 i)) : ℝ) /
        Real.sqrt n
  rw [hq]
  constructor
  · rintro ⟨v, hv, hfar⟩
    exact ⟨toCompanionLabel v, toCompanionLabel_mem x hx hv, hfar⟩
  · rintro ⟨w, hw, hfar⟩
    refine ⟨fromCompanionLabel w, (fromCompanionLabel_mem_iff x hx n w).mpr hw, fun i ↦ ?_⟩
    change ε < ((ReverseHistory.forestAt n 0 q.1).graph.dist
      (toCompanionLabel (fromCompanionLabel w)) (toCompanionLabel (q.2 i)) : ℝ) / Real.sqrt n
    rw [to_fromCompanionLabel]
    exact hfar i

/-- Leaf-tightness `eq:GH` for the actual forward uniform-attachment tree with
freezing and conditionally iid uniform vertices: for every `ε > 0`,
`lim_k limsup_n P(max_{v ∈ 𝕍ₙ} min_{i ≤ k} dⁿ(v, V_i)/√n > ε) = 0`, under
survival, `Lim^{1/2}_{1/f}` with `f > 0` a.e., and
`max_{1 ≤ k ≤ n} S^n_k = O(√n)`. -/
theorem forward_critical_leaf_tightness {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      TreeSampling.sampledForwardLaw (companionSchedule (x n)) n k
        {q | ∃ v ∈ q.1.vertices, ∀ i,
          ε < (q.1.graph.dist v (q.2 i) : ℝ) / Real.sqrt n}) atTop) atTop (𝓝 0) := by
  refine (critical_graphSampleNet_tightness hx hf hL1 hpop hε).congr' ?_
  refine Eventually.of_forall fun k ↦ limsup_congr ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨hxn, hsn⟩ := hx n hn
  have hext := (companion_before_extinction (x n) hxn hsn).le
  have hroot : Sum.inl 0 ∈ Freezing1.vertexLabels (companionSchedule (x n)) n := by
    simpa only [toCompanionLabel, Nat.sub_self] using
      toCompanionLabel_mem (x n) hxn (active_one_mem_vertexLabels (x n) hsn)
  rw [sampledReverseVectorLaw_leafEvent (x n) hxn hsn k ε]
  exact (TreeSampling.sampledForwardLaw_leafEvent _ n k hext hroot ε).symm

end Freezing2
