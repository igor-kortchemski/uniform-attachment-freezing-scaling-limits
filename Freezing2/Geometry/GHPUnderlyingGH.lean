module

public import Freezing2.Geometry.GHPTriangle
public import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Forgetting the measure contracts GHP to GH

Every measured ambient cost contains the ordinary Hausdorff cost of the same
isometric embeddings. Thus the exact Gromov--Hausdorff distance is bounded
by the exact measured infimum. In particular zero GHP distance forces a
whole-space isometry; preservation of the measure is a further obligation.
-/

@[expose] public section

open MeasureTheory Metric Set GromovHausdorff

universe u

namespace Freezing2

variable {X Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Nonempty Y]

/-- Forgetting the probability measure cannot increase the source distance. -/
theorem ghDist_le_ghpDistance (μ : Measure X) (ν : Measure Y) :
    ghDist X Y ≤ ghpDistance μ ν := by
  apply le_csInf (ghpCosts_nonempty μ ν)
  rintro r ⟨A, m, i, j, hi, hj, rfl⟩
  let := m
  let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace A := borel A
  exact (ghDist_le_hausdorffDist hi hj).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)

/-- Zero measured distance already forces an isometry of the entire compact
carriers, including any points outside the measure supports. -/
theorem nonempty_isometryEquiv_of_ghpDistance_eq_zero
    (μ : Measure X) (ν : Measure Y) (h : ghpDistance μ ν = 0) : Nonempty (X ≃ᵢ Y) := by
  apply toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
  apply dist_eq_zero.mp
  exact le_antisymm ((ghDist_le_ghpDistance μ ν).trans h.le) dist_nonneg

omit [Nonempty X] [Nonempty Y] in
/-- A measured isometry always gives zero distance. The converse additionally
requires proving that a zero-distance isometry can preserve the measures. -/
theorem ghpDistance_eq_zero_of_measured_isometry
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    (e : X ≃ᵢ Y) (he : μ.map e = ν) : ghpDistance μ ν = 0 := by
  rw [← he, ghpDistance_map_isometryEquiv_right, ghpDistance_self]

end Freezing2
