module

public import Freezing2.Geometry.GromovHausdorffProkhorov

/-!
# Transport of the source GHP infimum by measured isometries

Precomposition by a surjective isometry preserves each admissible ambient
cost, including both the pushed measure and the entire embedded image. Thus
the actual infimum is invariant, without assuming a quotient-space metric or
any Polish-space theorem.
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace Freezing2

variable {X X' Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace X'] [MeasurableSpace X'] [BorelSpace X'] [CompactSpace X']
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem ghpCosts_map_isometryEquiv_subset (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpCosts (μ.map e) ν ⊆ ghpCosts μ ν := by
  rintro r ⟨Z, m, i, j, hi, hj, hr⟩
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  refine ⟨Z, m, i ∘ e, j, hi.comp e.isometry, hj, ?_⟩
  rw [Measure.map_map hi.continuous.measurable e.continuous.measurable] at hr
  rw [e.surjective.range_comp i]
  exact hr

/-- The complete sets of allowed ambient costs coincide, not merely their
infima. The Borel structure in each witness is induced by its own metric. -/
theorem ghpCosts_map_isometryEquiv (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpCosts (μ.map e) ν = ghpCosts μ ν := by
  apply Set.Subset.antisymm (ghpCosts_map_isometryEquiv_subset μ ν e)
  have h := ghpCosts_map_isometryEquiv_subset (μ.map e) ν e.symm
  have he : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']
  rwa [he] at h

theorem ghpDistance_map_isometryEquiv (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpDistance (μ.map e) ν = ghpDistance μ ν := by
  simp only [ghpDistance, ghpCosts_map_isometryEquiv μ ν e]

/-- A measure-preserving isometry equivalence leaves the represented GHP
observable unchanged. No structural premise about a quotient is used. -/
theorem ghpDistance_eq_of_isometryEquiv (μ : Measure X) (μ' : Measure X')
    (ν : Measure Y) (e : X ≃ᵢ X') (hμ : μ.map e = μ') :
    ghpDistance μ ν = ghpDistance μ' ν := by
  rw [← hμ, ghpDistance_map_isometryEquiv]

theorem ghpCosts_comm (μ : Measure X) (ν : Measure Y) : ghpCosts μ ν = ghpCosts ν μ := by
  apply Set.Subset.antisymm
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    refine ⟨Z, m, j, i, hj, hi, ?_⟩
    simpa only [levyProkhorovDist_comm, hausdorffDist_comm] using hr
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    refine ⟨Z, m, j, i, hj, hi, ?_⟩
    simpa only [levyProkhorovDist_comm, hausdorffDist_comm] using hr

theorem ghpDistance_comm (μ : Measure X) (ν : Measure Y) :
    ghpDistance μ ν = ghpDistance ν μ := by
  simp only [ghpDistance, ghpCosts_comm μ ν]

/-- The same invariance holds in the right argument. -/
theorem ghpDistance_map_isometryEquiv_right (ν : Measure Y) (μ : Measure X) (e : X ≃ᵢ X') :
    ghpDistance ν (μ.map e) = ghpDistance ν μ := by
  rw [ghpDistance_comm ν, ghpDistance_map_isometryEquiv, ghpDistance_comm μ]

end Freezing2
