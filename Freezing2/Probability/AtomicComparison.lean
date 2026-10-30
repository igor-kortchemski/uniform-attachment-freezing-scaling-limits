module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Comparing countable probability laws on their positive atoms

Equality on the first law's positive atoms implies domination everywhere, and
normalization upgrades domination to equality. This avoids a separate
surjectivity proof when comparing two explicitly supported history laws.
-/

@[expose] public section

open MeasureTheory

namespace Freezing2

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Countable Ω]

/-- Singleton domination extends to all measurable sets on a countable space. -/
theorem measure_le_of_singleton_le {μ ν : Measure Ω}
    (h : ∀ a, μ {a} ≤ ν {a}) : μ ≤ ν := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [← Measure.tsum_indicator_apply_singleton μ s hs,
    ← Measure.tsum_indicator_apply_singleton ν s hs]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ s
  · simpa only [Set.indicator_of_mem ha] using h a
  · simp only [Set.indicator_of_notMem ha, le_refl]

/-- Probability normalization turns atomwise domination into equality. -/
theorem probability_eq_of_singleton_le {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a, μ {a} ≤ ν {a}) : μ = ν :=
  Measure.eq_of_le_of_isProbabilityMeasure (measure_le_of_singleton_le h)

/-- Matching every positive atom of the first law is sufficient. No premise
asserting that the two supports coincide is needed. -/
theorem probability_eq_of_agree_on_positive_atoms {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a, μ {a} ≠ 0 → μ {a} = ν {a}) : μ = ν := by
  apply probability_eq_of_singleton_le
  intro a
  by_cases ha : μ {a} = 0
  · simp only [ha, zero_le]
  · exact (h a ha).le

end Freezing2
