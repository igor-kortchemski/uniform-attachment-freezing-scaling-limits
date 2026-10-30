module

public import Freezing2.Geometry.GHPTransport
public import Freezing2.Probability.SubcriticalGHPLimit
public import Freezing2.Probability.CanonicalMetricTransport
public import Freezing2.Probability.ForwardReverseLaw

/-!
# Exact measured GHP transport from reverse to forward trees

The canonical timestamp bijection is a measure-preserving isometry between
the actual scaled finite trees, each equipped with uniform vertex measure.
Consequently their GHP observables to the source segment agree pointwise on
valid terminal forests. No forward/reverse equality in law is assumed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace Freezing2

/-- Uniform sampling on the true finite vertex subtype of a forward state. -/
noncomputable def forwardVertexMeasure (s : Freezing1.Forward.State) :
    Measure {v // v ∈ s.vertices} := Measure.uniformOfFinset Finset.univ

theorem forwardVertexMeasure_isProbabilityMeasure {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) : IsProbabilityMeasure (forwardVertexMeasure s) :=
  uniformOfFinset_probability_of_nonempty _ ⟨⟨0, hs.root_mem⟩, Finset.mem_univ _⟩

/-- The actual uniformly measured, scaled forward-tree GHP observable. The
fallback has no effect on valid forward trees with positive scale. -/
noncomputable def forwardGHPDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (c : ℝ) (s : Freezing1.Forward.State) : ℝ :=
  if h : s.tree.Connected ∧ 0 < c then
    letI := scaledGraphMetric s.tree h.1 c h.2
    ghpDistance (forwardVertexMeasure s) (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g))
  else 0

theorem measurable_forwardGHPDistance (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (c : ℝ) :
    Measurable (forwardGHPDistance g hg hpos c) := measurable_from_top

namespace ReverseStamped

/-- The canonical finite vertex bijection transports the whole uniform law. -/
theorem map_forestVertexMeasure_canonicalVertexEquiv
    {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    (forestVertexMeasure F.forest).map (canonicalVertexEquiv hF ht ho) =
      forwardVertexMeasure (canonicalForwardState x n F) := by
  unfold forestVertexMeasure forwardVertexMeasure
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
    (fun u _ v _ huv ↦ (canonicalVertexEquiv hF ht ho).injective huv)]
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact (canonicalVertexEquiv hF ht ho).surjective v

/-- The genuine scaled graph metrics are preserved by the canonical vertex
bijection. Both metrics use the same positive scaling constant. -/
noncomputable def canonicalScaledIsometry
    {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    (c : ℝ) (hc : 0 < c)
    (hconnF : F.forest.toGraph.Connected)
    (hconnS : (canonicalForwardState x n F).tree.Connected) :
    @IsometryEquiv {v // v ∈ F.forest.vertices}
      {v // v ∈ (canonicalForwardState x n F).vertices}
      (@PseudoMetricSpace.toPseudoEMetricSpace _
        (scaledGraphMetric F.forest.toGraph hconnF c hc).toPseudoMetricSpace)
      (@PseudoMetricSpace.toPseudoEMetricSpace _
        (scaledGraphMetric (canonicalForwardState x n F).tree hconnS c hc).toPseudoMetricSpace) := by
  letI : PseudoEMetricSpace {v // v ∈ F.forest.vertices} :=
    @PseudoMetricSpace.toPseudoEMetricSpace _
      (scaledGraphMetric F.forest.toGraph hconnF c hc).toPseudoMetricSpace
  letI : PseudoEMetricSpace {v // v ∈ (canonicalForwardState x n F).vertices} :=
    @PseudoMetricSpace.toPseudoEMetricSpace _
      (scaledGraphMetric (canonicalForwardState x n F).tree hconnS c hc).toPseudoMetricSpace
  exact
    { toEquiv := canonicalVertexEquiv hF ht ho
      isometry_toFun := @Isometry.of_dist_eq _ _
        (scaledGraphMetric F.forest.toGraph hconnF c hc).toPseudoMetricSpace
        (scaledGraphMetric (canonicalForwardState x n F).tree hconnS c hc).toPseudoMetricSpace
        (canonicalVertexEquiv hF ht ho) (by
          intro u v
          change c * ((canonicalForwardState x n F).tree.dist
            (canonicalTreeIso hF ht ho u) (canonicalTreeIso hF ht ho v) : ℝ) =
              c * (F.forest.toGraph.dist u v : ℝ)
          rw [graphIso_dist_eq (canonicalTreeIso hF ht ho) hconnF]) }

/-- Exact pointwise equality of the actual measured GHP observables, before
using the independently proved forward/reverse equality in law. -/
theorem forestGHPDistance_eq_forwardGHPDistance
    {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {c : ℝ} (hc : 0 < c) :
    forestGHPDistance g hg hpos c F.forest =
      forwardGHPDistance g hg hpos c (canonicalForwardState x n F) := by
  have hconnF : F.forest.toGraph.Connected :=
    (F.forest.isTree_of_one_root (one_root_of_terminal_valid hF) hF.acyclic).connected
  have hconnS : (canonicalForwardState x n F).tree.Connected :=
    (ForwardHistory.state_valid x (canonicalHistory x n F)).tree_connected
  rw [forestGHPDistance, dite_eq_left ⟨hconnF, hc⟩,
    forwardGHPDistance, dite_eq_left ⟨hconnS, hc⟩]
  let := scaledGraphMetric F.forest.toGraph hconnF c hc
  let := scaledGraphMetric (canonicalForwardState x n F).tree hconnS c hc
  exact ghpDistance_eq_of_isometryEquiv (forestVertexMeasure F.forest)
    (forwardVertexMeasure (canonicalForwardState x n F))
    (profileSegmentMeasure g hg hpos : Measure (ProfileSegment g))
    (canonicalScaledIsometry hF ht ho c hc hconnF hconnS)
    (by simpa only [canonicalScaledIsometry, IsometryEquiv.coe_mk] using
      map_forestVertexMeasure_canonicalVertexEquiv hF ht ho)

/-- All deterministic transport premises hold under the actual stamped
terminal reverse law. -/
theorem treeLaw_forestGHPDistance_eq_forwardGHPDistance
    (x : Freezing1.SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {c : ℝ} (hc : 0 < c) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n,
      forestGHPDistance g hg hpos c F.forest =
        forwardGHPDistance g hg hpos c (canonicalForwardState x n F) := by
  filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
    Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
    treeLaw_canonicalOrder x n hn] with F hF ht ho
  exact forestGHPDistance_eq_forwardGHPDistance
    (by simpa only [Nat.sub_self] using hF) ht ho hg hpos hc

/-- Exact equality in law of the measured GHP observables for the two actual
constructions, using the proved canonical isometry and N01. -/
theorem map_reverse_treeLaw_forestGHPDistance_eq_forward
    (x : Freezing1.SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {c : ℝ} (hc : 0 < c) :
    (Freezing1.Reverse.treeLaw x n).map (forestGHPDistance g hg hpos c) =
      (Freezing1.Forward.treeLaw x n).map (forwardGHPDistance g hg hpos c) := by
  rw [← Freezing1.ReverseStamped.map_treeLaw]
  rw [Measure.map_map measurable_from_top measurable_from_top]
  calc
    (Freezing1.ReverseStamped.treeLaw x n).map
        ((forestGHPDistance g hg hpos c) ∘ Freezing1.ReverseStamped.Forest.forest) =
      (Freezing1.ReverseStamped.treeLaw x n).map
        ((forwardGHPDistance g hg hpos c) ∘ canonicalForwardState x n) :=
      Measure.map_congr (treeLaw_forestGHPDistance_eq_forwardGHPDistance x n hn hg hpos hc)
    _ = _ := by
      rw [← Measure.map_map (measurable_forwardGHPDistance g hg hpos c) measurable_from_top,
        forward_reverse_same_law x n hn]

end ReverseStamped
end Freezing2
