module

public import Freezing2.Analysis.LocalL1

/-!
# Integrals on shrinking sets under L¹ convergence

The local square-profile argument uses intervals whose lengths tend to zero.
This lemma keeps that moving set separate from convergence of the integrands.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- Integrals of an L¹-convergent family over sets of vanishing measure tend
to zero. No sign, finite total measure, or nesting hypothesis is needed. -/
theorem tendsto_integral_on_small_sets_of_l1 {Ω κ : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : κ → Ω → ℝ} {g : Ω → ℝ} {l : Filter κ}
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ)
    (hL1 : Tendsto (fun i ↦ ∫ x, |f i x - g x| ∂μ) l (𝓝 0))
    {s : κ → Set Ω} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x in s i, f i x ∂μ) l (𝓝 0) := by
  have hsmall := hg.tendsto_setIntegral_nhds_zero hs
  have hdiff : Tendsto (fun i ↦ |(∫ x in s i, f i x ∂μ) -
      ∫ x in s i, g x ∂μ|) l (𝓝 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _) (fun i ↦
      abs_setIntegral_sub_le_integral_abs_sub (hf i) hg (s i)) hL1
  have hdiff' := (tendsto_zero_iff_abs_tendsto_zero _).mpr hdiff
  convert hdiff'.add hsmall using 1 <;> simp

end Freezing2
