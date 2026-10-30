module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic

/-!
# Weak convergence with a common dominating measure

Uniform domination upgrades weak convergence to convergence against every
integrable test function. Consequently a merely measurable map, including the
square of the manuscript's limiting reciprocal profile, can be applied to the
converging laws. The proof approximates each test in L1 by a bounded continuous
function; it does not require continuity of the profile.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace Freezing2

/-- The L1 error under a dominated measure is bounded by the same error under
the reference measure times the domination constant. -/
theorem integral_norm_le_of_measure_le_smul {A : Type*} [MeasurableSpace A]
    {μ ν : Measure A} {c : ℝ≥0} {f : A → ℝ} (hf : Integrable f μ)
    (hν : ν ≤ (c : ℝ≥0∞) • μ) :
    (∫ x, ‖f x‖ ∂ν) ≤ (c : ℝ) * ∫ x, ‖f x‖ ∂μ := by
  calc
    (∫ x, ‖f x‖ ∂ν) ≤ ∫ x, ‖f x‖ ∂((c : ℝ≥0∞) • μ) :=
      integral_mono_measure hν (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
        hf.norm.smul_measure_nnreal
    _ = (c : ℝ) * ∫ x, ‖f x‖ ∂μ := by
      rw [integral_smul_measure]
      simp

/-- A useful signed-integral version of the domination estimate. -/
theorem abs_integral_sub_le_of_measure_le_smul {A : Type*} [MeasurableSpace A]
    {μ ν : Measure A} {c : ℝ≥0} {f g : A → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hν : ν ≤ (c : ℝ≥0∞) • μ) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤
      (c : ℝ) * ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← integral_sub (hf.smul_measure_nnreal.mono_measure hν)
    (hg.smul_measure_nnreal.mono_measure hν), ← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_le_of_measure_le_smul (hf.sub hg) hν)

/-- Weakly convergent probability laws dominated by one fixed finite regular
measure converge against all tests integrable for that reference measure. -/
theorem tendsto_integral_of_weak_of_dominated
    {A : Type*} [TopologicalSpace A] [NormalSpace A]
    [MeasurableSpace A] [BorelSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {νs : ℕ → ProbabilityMeasure A} {ν : ProbabilityMeasure A} {c : ℝ≥0}
    (hlim : Tendsto νs atTop (𝓝 ν))
    (hdom : ∀ᶠ n in atTop, (νs n : Measure A) ≤ (c : ℝ≥0∞) • μ)
    (hν : (ν : Measure A) ≤ (c : ℝ≥0∞) • μ)
    {f : A → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(νs n : Measure A)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure A))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * ((c : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgInt⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hgLim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
  have hgNear : ∀ᶠ n in atTop,
      |(∫ x, g x ∂(νs n : Measure A)) - ∫ x, g x ∂(ν : Measure A)| < ε / 2 := by
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hgLim (ε / 2) (half_pos hε))
  have hsmall : 2 * (c : ℝ) * δ < ε / 2 := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 4 * ((c : ℝ) + 1))]
    nlinarith
  filter_upwards [hdom, hgNear] with n hn hgn
  have hleft := (abs_integral_sub_le_of_measure_le_smul hf hgInt hn).trans
    (mul_le_mul_of_nonneg_left hg c.coe_nonneg)
  have hright := (abs_integral_sub_le_of_measure_le_smul hf hgInt hν).trans
    (mul_le_mul_of_nonneg_left hg c.coe_nonneg)
  rw [Real.dist_eq]
  calc
    |(∫ x, f x ∂(νs n : Measure A)) - ∫ x, f x ∂(ν : Measure A)| ≤
        |(∫ x, f x ∂(νs n : Measure A)) - ∫ x, g x ∂(νs n : Measure A)| +
        |(∫ x, g x ∂(νs n : Measure A)) - ∫ x, g x ∂(ν : Measure A)| +
        |(∫ x, g x ∂(ν : Measure A)) - ∫ x, f x ∂(ν : Measure A)| := by
      have h1 := dist_triangle (∫ x, f x ∂(νs n : Measure A))
        (∫ x, g x ∂(νs n : Measure A)) (∫ x, f x ∂(ν : Measure A))
      have h2 := dist_triangle (∫ x, g x ∂(νs n : Measure A))
        (∫ x, g x ∂(ν : Measure A)) (∫ x, f x ∂(ν : Measure A))
      simp only [Real.dist_eq] at h1 h2
      linarith
    _ < ε := by
      rw [abs_sub_comm (∫ x, g x ∂(ν : Measure A))] 
      linarith

/-- Under common domination, applying a merely measurable map preserves weak
convergence. This is stronger than the continuous mapping theorem precisely
because of the additional domination hypothesis. -/
theorem tendsto_probabilityMap_of_weak_of_dominated
    {A : Type*} [TopologicalSpace A] [NormalSpace A]
    [MeasurableSpace A] [BorelSpace A]
    {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    {μ : Measure A} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {νs : ℕ → ProbabilityMeasure A} {ν : ProbabilityMeasure A} {c : ℝ≥0}
    (hlim : Tendsto νs atTop (𝓝 ν))
    (hdom : ∀ᶠ n in atTop, (νs n : Measure A) ≤ (c : ℝ≥0∞) • μ)
    (hν : (ν : Measure A) ≤ (c : ℝ≥0∞) • μ)
    {H : A → B} (hH : Measurable H) :
    Tendsto (fun n ↦ (νs n).map H) atTop (𝓝 (ν.map H)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hInt : Integrable (fun x ↦ φ (H x)) μ :=
    (φ.integrable (μ.map H)).comp_measurable hH
  have ht := tendsto_integral_of_weak_of_dominated hlim hdom hν hInt
  simpa only [ProbabilityMeasure.toMeasure_map,
    integral_map hH.aemeasurable φ.continuous.aestronglyMeasurable] using ht

end Freezing2
