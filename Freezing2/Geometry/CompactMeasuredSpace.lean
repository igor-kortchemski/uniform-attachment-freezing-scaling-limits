module

public import Freezing2.Geometry.GHPTransport

/-!
# Represented compact metric probability spaces

The carrier, its genuine metric, compactness, and Borel probability measure
are bundled together. Nonempty carriers are explicit. The Borel condition
prevents a separate measurable structure from changing the intended measure.
-/

@[expose] public section

open MeasureTheory

universe u

namespace Freezing2

/-- A nonempty compact metric space equipped with a Borel probability measure.
Carriers lie in one fixed universe; the type of all represented spaces lies in
the next universe. No full-support assumption is imposed. -/
structure CompactMeasuredSpace where
  carrier : Type u
  metric : MetricSpace carrier
  nonempty : Nonempty carrier
  compact : @CompactSpace carrier metric.toUniformSpace.toTopologicalSpace
  measurable : MeasurableSpace carrier
  borel : @BorelSpace carrier metric.toUniformSpace.toTopologicalSpace measurable
  law : @ProbabilityMeasure carrier measurable

namespace CompactMeasuredSpace

instance : CoeSort CompactMeasuredSpace.{u} (Type u) := ⟨carrier⟩
instance (X : CompactMeasuredSpace) : MetricSpace X := X.metric
instance (X : CompactMeasuredSpace) : Nonempty X := X.nonempty
instance (X : CompactMeasuredSpace) : CompactSpace X := X.compact
instance (X : CompactMeasuredSpace) : MeasurableSpace X := X.measurable
instance (X : CompactMeasuredSpace) : BorelSpace X := X.borel

/-- Bundle an existing space and its actual probability measure. -/
def of (X : Type u) [MetricSpace X] [Nonempty X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) : CompactMeasuredSpace.{u} where
  carrier := X
  metric := inferInstance
  nonempty := inferInstance
  compact := inferInstance
  measurable := inferInstance
  borel := inferInstance
  law := μ

/-- The exact manuscript GHP infimum on represented spaces. -/
noncomputable def distance (X Y : CompactMeasuredSpace.{u}) : ℝ :=
  ghpDistance (X.law : Measure X) (Y.law : Measure Y)

theorem distance_nonneg (X Y : CompactMeasuredSpace.{u}) : 0 ≤ distance X Y :=
  ghpDistance_nonneg _ _

theorem distance_comm (X Y : CompactMeasuredSpace.{u}) : distance X Y = distance Y X :=
  ghpDistance_comm _ _

/-- Exact agreement with the original infimum, with no surrogate distance. -/
theorem distance_of (X Y : Type u) [MetricSpace X] [Nonempty X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [Nonempty Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    distance (of X μ) (of Y ν) = ghpDistance (μ : Measure X) (ν : Measure Y) := rfl

end CompactMeasuredSpace
end Freezing2
