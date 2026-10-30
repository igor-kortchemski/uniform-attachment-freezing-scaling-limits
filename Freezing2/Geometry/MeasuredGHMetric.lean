module

public import Freezing2.Geometry.MeasuredGHSpace
public import Freezing2.Geometry.GHPSeparation

/-!
# The genuine GHP metric on whole-space measured isometry classes

The already constructed quotient and its topology are unchanged. Zero exact
GHP distance forces a measure-preserving isometry, so the existing
pseudometric is a metric. Completeness and separability remain separate.
-/

@[expose] public section

open MeasureTheory

universe u

namespace Freezing2.MeasuredGHSpace

/-- Separation upgrades the exact existing quotient pseudometric. Its distance,
uniformity, topology and Borel structure are preserved definitionally. -/
noncomputable instance : MetricSpace MeasuredGHSpace.{u} where
  toPseudoMetricSpace := instPseudoMetricSpace
  eq_of_dist_eq_zero := by
    intro X Y h
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        apply Quotient.sound
        exact (ghpDistance_eq_zero_iff_measured_isometry (X.law : Measure X)
          (Y.law : Measure Y)).mp h

end Freezing2.MeasuredGHSpace
