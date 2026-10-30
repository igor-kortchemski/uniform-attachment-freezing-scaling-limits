module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Event bounds under independent sampling

An event on a product probability space is bounded by the probability of a
bad parameter set plus a uniform conditional bound outside that set. This is
used for actual randomly sampled vertices, retaining collision contributions.
-/

@[expose] public section

open Filter MeasureTheory

namespace Freezing2

variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
  {μ : Measure Ω} {ν : Measure P} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
theorem integral_indicator_section {E : Set (Ω × P)} (hE : MeasurableSet E) (p : P) :
    (∫ ω, E.indicator (fun _ ↦ (1 : ℝ)) (ω, p) ∂μ) =
      μ.real {ω | (ω, p) ∈ E} := by
  classical
  have he : (fun ω ↦ E.indicator (fun _ ↦ (1 : ℝ)) (ω, p)) =
      ({ω | (ω, p) ∈ E}).indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [he]
  exact integral_indicator_one (hE.preimage (measurable_id.prodMk measurable_const))

theorem measureReal_prod_eq_integral_sections {E : Set (Ω × P)} (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ p, μ.real {ω | (ω, p) ∈ E} ∂ν := by
  calc
    _ = ∫ q, E.indicator (fun _ ↦ (1 : ℝ)) q ∂μ.prod ν :=
      (integral_indicator_one hE).symm
    _ = ∫ p, ∫ ω, E.indicator (fun _ ↦ (1 : ℝ)) (ω, p) ∂μ ∂ν :=
      integral_prod_symm _ ((integrable_const (1 : ℝ)).indicator hE)
    _ = _ := integral_congr_ae (Eventually.of_forall (integral_indicator_section hE))

/-- A uniform bound outside a bad parameter event remains valid after actual
independent sampling. The bad event's probability is explicitly retained. -/
theorem measureReal_prod_event_le_bad_add {E : Set (Ω × P)} (hE : MeasurableSet E)
    {B : Set P} (hB : MeasurableSet B) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ᵐ p ∂ν, p ∉ B → μ.real {ω | (ω, p) ∈ E} ≤ η) :
    (μ.prod ν).real E ≤ ν.real B + η := by
  classical
  have hf : Integrable (fun p ↦ μ.real {ω | (ω, p) ∈ E}) ν := by
    have hi := ((integrable_const (1 : ℝ) : Integrable (fun _ : Ω × P ↦ (1 : ℝ))
      (μ.prod ν)).indicator hE).integral_prod_right
    simpa only [integral_indicator_section hE] using hi
  have hBint : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hB
  rw [measureReal_prod_eq_integral_sections hE]
  calc
    _ ≤ ∫ p, B.indicator (fun _ ↦ (1 : ℝ)) p + η ∂ν := by
      apply integral_mono_ae hf (hBint.add (integrable_const η))
      filter_upwards [hbound] with p hp
      change μ.real {ω | (ω, p) ∈ E} ≤ B.indicator (fun _ ↦ (1 : ℝ)) p + η
      by_cases hmem : p ∈ B
      · simpa only [Set.indicator_of_mem hmem] using
          (measureReal_le_one (μ := μ) (s := {ω | (ω, p) ∈ E})).trans (by linarith)
      · simpa only [Set.indicator_of_notMem hmem, zero_add] using hp hmem
    _ = _ := by
      have hiB : (∫ p, B.indicator (fun _ ↦ (1 : ℝ)) p ∂ν) = ν.real B :=
        integral_indicator_one hB
      rw [integral_add hBint (integrable_const η), hiB]
      simp

end Freezing2
