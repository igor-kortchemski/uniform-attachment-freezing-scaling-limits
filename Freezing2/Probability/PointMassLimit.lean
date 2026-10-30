module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak convergence to a deterministic point on varying probability spaces

A vanishing metric tail implies weak convergence to the point mass without
assuming separability or a common underlying probability space. This applies
to represented compact measured spaces before establishing their global
separability or completing the isometry-class construction.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace Freezing2

/-- Vanishing distance tails to a fixed point imply genuine weak convergence
of probability laws. No countability assumption on the target is needed. -/
theorem tendsto_probabilityMap_const_of_tail
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {F : (n : ℕ) → Ω n → E}
    (hF : ∀ n, Measurable (F n)) (c : E)
    (htail : ∀ ε > 0, Tendsto (fun n ↦
      (μ n : Measure (Ω n)).real {ω | ε < dist (F n ω) c}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (μ n).map (F n)) atTop
      (𝓝 (⟨Measure.dirac c, inferInstance⟩ : ProbabilityMeasure E)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hInt (n : ℕ) : Integrable (fun ω ↦ φ (F n ω)) (μ n : Measure (Ω n)) :=
    (φ.integrable ((μ n : Measure (Ω n)).map (F n))).comp_measurable (hF n)
  have hlim : Tendsto (fun n ↦ ∫ ω, φ (F n ω) ∂(μ n : Measure (Ω n)))
      atTop (𝓝 (φ c)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp φ.continuous.continuousAt
      (ε / 2) (half_pos hε)
    let δ := r / 2
    have hδ : 0 < δ := half_pos hr
    let B := 2 * ‖φ‖
    have ht : ∀ᶠ n in atTop, B * (μ n : Measure (Ω n)).real
        {ω | δ < dist (F n ω) c} < ε / 2 := by
      have h := (htail δ hδ).const_mul B
      apply h.eventually_lt_const
      simpa using half_pos hε
    filter_upwards [ht] with n hn
    let A := {ω | δ < dist (F n ω) c}
    have hA : MeasurableSet A := measurableSet_lt measurable_const
      (((continuous_id.dist continuous_const).measurable).comp (hF n))
    have hpt (ω : Ω n) : ‖φ (F n ω) - φ c‖ ≤
        ε / 2 + A.indicator (fun _ ↦ B) ω := by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hb : ‖φ (F n ω) - φ c‖ ≤ B := by
          calc
            _ ≤ ‖φ (F n ω)‖ + ‖φ c‖ := norm_sub_le _ _
            _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _)
            _ = B := by dsimp [B]; ring
        exact hb.trans (le_add_of_nonneg_left (half_pos hε).le)
      · rw [Set.indicator_of_notMem hω, add_zero]
        have hd : dist (F n ω) c < r :=
          (le_of_not_gt hω).trans_lt (by dsimp [δ]; linarith)
        simpa only [dist_eq_norm] using (hclose hd).le
    have hbound : dist (∫ ω, φ (F n ω) ∂(μ n : Measure (Ω n))) (φ c) ≤
        ε / 2 + B * (μ n : Measure (Ω n)).real A := by
      have hc : φ c = ∫ _ω : Ω n, φ c ∂(μ n : Measure (Ω n)) := by simp
      rw [dist_eq_norm, hc,
        ← integral_sub (hInt n) (integrable_const _)]
      calc
        _ ≤ ∫ ω, ‖φ (F n ω) - φ c‖ ∂(μ n : Measure (Ω n)) :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ ω, ε / 2 + A.indicator (fun _ ↦ B) ω ∂(μ n : Measure (Ω n)) :=
          integral_mono ((hInt n).sub (integrable_const _)).norm
            ((integrable_const _).add ((integrable_const B).indicator hA)) hpt
        _ = ε / 2 + B * (μ n : Measure (Ω n)).real A := by
          rw [integral_add (integrable_const _) ((integrable_const B).indicator hA),
            integral_indicator_const B hA]
          simp [smul_eq_mul, mul_comm]
    exact hbound.trans_lt (by change B * (μ n : Measure (Ω n)).real A < ε / 2 at hn; linarith)
  simpa only [ProbabilityMeasure.toMeasure_map, integral_map (hF _).aemeasurable
    φ.continuous.aestronglyMeasurable, ProbabilityMeasure.coe_mk,
    integral_dirac' (φ : E → ℝ) c φ.continuous.stronglyMeasurable] using hlim

end Freezing2
