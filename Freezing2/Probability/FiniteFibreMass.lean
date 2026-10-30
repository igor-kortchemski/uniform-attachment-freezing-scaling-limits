module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Tactic

/-!
# Exact masses from finite almost-sure fibres

Finite fibres of a measurable map have mass equal to the sum of their atoms.
An almost-sure support restriction is sufficient; irrelevant points outside
that support need not satisfy a global fibre identity.
-/

@[expose] public section

open MeasureTheory

namespace Freezing2

variable {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass B]

omit [MeasurableSingletonClass Ω] in
/-- A positive image atom contains a point of every full-measure support. -/
theorem exists_supported_preimage_of_map_atom_ne_zero {μ : Measure Ω} {f : Ω → B}
    (hf : Measurable f) {P : Ω → Prop} (hP : ∀ᵐ a ∂μ, P a) {b : B}
    (hb : μ.map f {b} ≠ 0) : ∃ a, P a ∧ f a = b := by
  by_contra hnone
  have hae : ∀ᵐ a ∂μ, f a ≠ b := by
    filter_upwards [hP] with a ha
    intro hab
    exact hnone ⟨a, ha, hab⟩
  have hz : μ (f ⁻¹' {b}) = 0 := by
    simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using ae_iff.mp hae
  rw [Measure.map_apply hf (measurableSet_singleton b), hz] at hb
  exact hb rfl

/-- If an image fibre agrees almost surely with a finite equal-mass set,
its real probability is the finite cardinality times the atom mass. -/
theorem map_real_singleton_eq_card_mul {μ : Measure Ω} [SigmaFinite μ]
    {f : Ω → B} (hf : Measurable f) {b : B} (s : Finset Ω) (w : ℝ)
    (hFibre : f ⁻¹' {b} =ᵐ[μ] (s : Set Ω))
    (hMass : ∀ a ∈ s, μ.real {a} = w) :
    (μ.map f).real {b} = (s.card : ℝ) * w := by
  change ((μ.map f) {b}).toReal = _
  rw [Measure.map_apply hf (measurableSet_singleton b)]
  change μ.real (f ⁻¹' {b}) = _
  rw [measureReal_congr hFibre, ← sum_measureReal_singleton]
  calc
    ∑ a ∈ s, μ.real {a} = ∑ _a ∈ s, w := Finset.sum_congr rfl hMass
    _ = _ := by simp

end Freezing2
