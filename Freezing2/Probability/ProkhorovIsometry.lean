module

public import Freezing2.Probability.ProkhorovBounds

/-!
# Prokhorov distance under compact isometric embeddings

A compact isometric image is Borel, so every source Borel test set can be
transported to the ambient space. Its thickening has exactly the original
preimage. Together with contraction this gives equality of Prokhorov distances.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Freezing2

theorem preimage_thickening_image_of_isometry
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hf : Isometry f) (r : ℝ) (B : Set X) :
    f ⁻¹' thickening r (f '' B) = thickening r B := by
  ext x
  simp only [Set.mem_preimage, mem_thickening_iff]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨y, hy, by simpa only [hf.dist_eq] using hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, by simpa only [hf.dist_eq] using hxy⟩

/-- A compact isometric embedding preserves the full extended Prokhorov
distance, not merely its vanishing or topology. -/
theorem levyProkhorovEDist_map_isometry
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Isometry f) :
    levyProkhorovEDist (μ.map f) (ν.map f) = levyProkhorovEDist μ ν := by
  apply le_antisymm (levyProkhorovEDist_map_le μ ν hf.lipschitzWith)
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε _ hB
  have hm : MeasurableEmbedding f := hf.isClosedEmbedding.measurableEmbedding
  have hi : MeasurableSet (f '' B) := hm.measurableSet_image.mpr hB
  have h := left_measure_le_of_levyProkhorovEDist_lt hε hi
  rw [Measure.map_apply hf.continuous.measurable hi,
    Measure.map_apply hf.continuous.measurable isOpen_thickening.measurableSet,
    hf.injective.preimage_image, preimage_thickening_image_of_isometry hf] at h
  exact h

/-- The real Prokhorov distance is likewise unchanged. -/
theorem levyProkhorovDist_map_isometry
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Isometry f) :
    levyProkhorovDist (μ.map f) (ν.map f) = levyProkhorovDist μ ν :=
  congrArg ENNReal.toReal (levyProkhorovEDist_map_isometry μ ν hf)

end Freezing2
