module

public import Freezing2.Geometry.MeasuredGluing

/-!
# The manuscript's Gromov--Hausdorff--Prokhorov infimum

The cost is the sum, as in the manuscript, of Prokhorov and Hausdorff distances
after isometric embeddings in one ambient metric space. Both spaces and all
ambient realizations are taken in the same universe. This defines the distance
on represented compact measured spaces; quotient and Polish-space properties
are separate background obligations.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Topology

universe u

namespace Freezing2

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

/-- All costs allowed by the exact source infimum over common metric spaces
and isometric embeddings. The ambient measure structure is its Borel structure. -/
def ghpCosts [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : Set ℝ :=
  {r | ∃ Z : Type u, ∃ m : MetricSpace Z,
    letI := m
    letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace Z := borel Z
    ∃ i : X → Z, ∃ j : Y → Z, Isometry i ∧ Isometry j ∧
      r = levyProkhorovDist (μ.map i) (ν.map j) + hausdorffDist (range i) (range j)}

/-- The source's GHP infimum, before passage to isometry classes. -/
noncomputable def ghpDistance [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : ℝ := sInf (ghpCosts μ ν)

variable [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]

theorem ghpCosts_bddBelow (μ : Measure X) (ν : Measure Y) : BddBelow (ghpCosts μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg

theorem ghpCosts_nonempty (μ : Measure X) (ν : Measure Y) : (ghpCosts μ ν).Nonempty := by
  let : MetricSpace (X ⊕ Y) := metricSpaceSum
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  refine ⟨_, X ⊕ Y, inferInstance, @Sum.inl X Y, @Sum.inr X Y, ?_, ?_, rfl⟩
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl

theorem ghpDistance_nonneg (μ : Measure X) (ν : Measure Y) : 0 ≤ ghpDistance μ ν := by
  apply le_csInf (ghpCosts_nonempty μ ν)
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg

/-- Any genuine common ambient realization gives an upper bound for the
source distance. No distortion surrogate is used in its definition. -/
theorem ghpDistance_le_of_isometries (μ : Measure X) (ν : Measure Y)
    (Z : Type u) [MetricSpace Z] (i : X → Z) (j : Y → Z)
    (hi : Isometry i) (hj : Isometry j) :
    letI : MeasurableSpace Z := borel Z
    ghpDistance μ ν ≤ levyProkhorovDist (μ.map i) (ν.map j) +
      hausdorffDist (range i) (range j) := by
  apply csInf_le (ghpCosts_bddBelow μ ν)
  exact ⟨Z, inferInstance, i, j, hi, hj, rfl⟩

/-- A measurable map with small distortion, dense image, and close pushed
measure gives the usual quantitative upper bound in the exact GHP distance. -/
theorem ghpDistance_le_of_approx [Nonempty X] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) {δ r p : ℝ} (hδ : 0 < δ)
    (hdis : ∀ x x', |dist x x' - dist (f x) (f x')| ≤ 2 * δ)
    (hdense : ∀ y, ∃ x, dist y (f x) ≤ r)
    (hprob : levyProkhorovDist (μ.map f) ν ≤ p) :
    ghpDistance μ ν ≤ 2 * δ + r + p := by
  obtain ⟨m, hl, hr, hH, hP⟩ := exists_measured_gluing μ ν f hf hδ hdis hdense hprob
  let := m
  let : TopologicalSpace (X ⊕ Y) := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  have h := ghpDistance_le_of_isometries μ ν (X ⊕ Y) (@Sum.inl X Y) (@Sum.inr X Y) hl hr
  calc
    _ ≤ levyProkhorovDist (μ.map (@Sum.inl X Y)) (ν.map (@Sum.inr X Y)) +
        hausdorffDist (range (@Sum.inl X Y)) (range (@Sum.inr X Y)) := h
    _ ≤ (δ + p) + (δ + r) := add_le_add hP hH
    _ = 2 * δ + r + p := by ring

end Freezing2
