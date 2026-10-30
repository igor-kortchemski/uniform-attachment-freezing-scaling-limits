module

public import Freezing2.Geometry.GHPCompactness
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Tightness transfer between measured spaces and their underlying carriers

The underlying GH projection is continuous and has compact inverse images.
Consequently a family of laws on whole-space measured-isometry classes is
tight exactly when its underlying GH laws are tight. The result does not
require full support of any of the random measures on the carriers.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace GromovHausdorff

universe u

namespace Freezing2.MeasuredGHSpace

/-- Tight underlying carrier laws give tight measured-space laws because
the inverse image of each compact GH set is compact in the exact GHP metric. -/
theorem isTightMeasureSet_of_underlyingGH
    {S : Set (Measure MeasuredGHSpace.{u})}
    (h : letI : MeasurableSpace GHSpace := borel GHSpace
      IsTightMeasureSet (Measure.map underlyingGH '' S)) : IsTightMeasureSet S := by
  let : MeasurableSpace GHSpace := borel GHSpace
  let : BorelSpace GHSpace := ⟨rfl⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h ⊢
  intro ε hε
  obtain ⟨K, hK, hmass⟩ := h ε hε
  refine ⟨underlyingGH ⁻¹' K, isCompact_preimage_underlyingGH hK, ?_⟩
  intro μ hμ
  have hm := hmass (μ.map underlyingGH) (mem_image_of_mem _ hμ)
  rw [Measure.map_apply continuous_underlyingGH.measurable hK.measurableSet.compl] at hm
  exact hm

/-- The continuous underlying projection preserves tightness and, by its
compact inverse-image property, also reflects it. -/
theorem isTightMeasureSet_iff_underlyingGH
    (S : Set (Measure MeasuredGHSpace.{u})) :
    IsTightMeasureSet S ↔
      letI : MeasurableSpace GHSpace := borel GHSpace
      IsTightMeasureSet (Measure.map underlyingGH '' S) := by
  let : MeasurableSpace GHSpace := borel GHSpace
  let : BorelSpace GHSpace := ⟨rfl⟩
  exact ⟨fun h ↦ h.map continuous_underlyingGH, isTightMeasureSet_of_underlyingGH⟩

/-- The indexed-family form used for distributions of random measured
spaces, retaining the original measures and exact projection pushforwards. -/
theorem isTightMeasureSet_range_iff_underlyingGH {ι : Type*}
    (μ : ι → Measure MeasuredGHSpace.{u}) :
    IsTightMeasureSet (range μ) ↔
      letI : MeasurableSpace GHSpace := borel GHSpace
      IsTightMeasureSet (range (fun i ↦ (μ i).map underlyingGH)) := by
  let : MeasurableSpace GHSpace := borel GHSpace
  simpa only [← range_comp, Function.comp_def] using isTightMeasureSet_iff_underlyingGH (range μ)

/-- Prokhorov's theorem turns tight underlying GH laws into compact closure
of a family of probability laws on the genuine GHP space. -/
theorem isCompact_closure_of_underlyingGH_tight
    {S : Set (ProbabilityMeasure MeasuredGHSpace.{u})}
    (h : letI : MeasurableSpace GHSpace := borel GHSpace
      IsTightMeasureSet (Measure.map underlyingGH ''
        {((μ : ProbabilityMeasure MeasuredGHSpace.{u}) : Measure MeasuredGHSpace.{u}) | μ ∈ S})) :
    IsCompact (closure S) :=
  isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_of_underlyingGH h)

end Freezing2.MeasuredGHSpace
