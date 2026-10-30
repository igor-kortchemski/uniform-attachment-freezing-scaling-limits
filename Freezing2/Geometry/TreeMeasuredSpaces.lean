module

public import Freezing2.Geometry.CompactMeasuredSpace
public import Freezing2.Probability.ForwardGHPTransport

/-!
# The actual finite tree and limiting segment as measured spaces

These bundles retain the genuine scaled graph metric and the uniform measure
on every vertex. The segment carries the exact profile image probability.
Totalization outside the connected positive-scale domain is harmless on the
actual tree laws, where that domain is proved separately.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace Freezing2

noncomputable def singletonMeasuredSpace : CompactMeasuredSpace :=
  CompactMeasuredSpace.of Unit ⟨Measure.dirac (), inferInstance⟩

/-- The genuine forward graph with positive scaling, bundled with its uniform
vertex measure. The fallback is a singleton only outside its stated domain. -/
noncomputable def forwardMeasuredSpace (c : ℝ) (s : Freezing1.Forward.State) :
    CompactMeasuredSpace :=
  if h : s.tree.Connected ∧ 0 < c then
    letI := scaledGraphMetric s.tree h.1 c h.2
    letI := h.1.nonempty
    letI : IsProbabilityMeasure (forwardVertexMeasure s) :=
      uniformOfFinset_probability_of_nonempty _ Finset.univ_nonempty
    CompactMeasuredSpace.of {v // v ∈ s.vertices} ⟨forwardVertexMeasure s, inferInstance⟩
  else singletonMeasuredSpace

/-- The source segment with the source profile image measure. -/
noncomputable def profileMeasuredSegment (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) : CompactMeasuredSpace :=
  letI := profileSegment_nonempty hg hpos
  CompactMeasuredSpace.of (ProfileSegment g) (profileSegmentMeasure g hg hpos)

/-- The bundled-space distance is exactly the already proved observable. -/
theorem forwardMeasuredSpace_distance_profile
    (g : ℝ → ℝ) (hg : Integrable g profileMeasure) (hpos : PositiveProfile g)
    {c : ℝ} (hc : 0 < c) {s : Freezing1.Forward.State} (hs : s.tree.Connected) :
    CompactMeasuredSpace.distance (forwardMeasuredSpace c s) (profileMeasuredSegment g hg hpos) =
      forwardGHPDistance g hg hpos c s := by
  rw [forwardMeasuredSpace, dite_eq_left (show s.tree.Connected ∧ 0 < c from ⟨hs, hc⟩),
    forwardGHPDistance, dite_eq_left (show s.tree.Connected ∧ 0 < c from ⟨hs, hc⟩)]
  rfl

end Freezing2
