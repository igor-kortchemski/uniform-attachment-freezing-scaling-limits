module

public import Freezing2.Analysis.LocalL1
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# From second moments to L¹ convergence of squares

Under `L¹` convergence of real functions, convergence of their second moments
is equivalent to `L¹` convergence of their squares. The measure is arbitrary,
so the statement applies directly on any of the fixed interior intervals in
the paper's reciprocal-square hypothesis.

The proof uses the subsequence criterion for convergence, almost-everywhere
subsequences of convergence in measure, and dominated convergence for
`min(fₙ²,g²)`. This is the usual Scheffé argument; nonnegativity of the original
functions is not needed. Integrability is explicit throughout.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Convert the integral formulation of `L¹` convergence to convergence in measure. -/
theorem tendstoInMeasure_of_integral_abs_sub {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hL1 : Tendsto (fun n ↦ ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have h := ENNReal.tendsto_ofReal hL1
  simp only [ENNReal.ofReal_zero] at h
  convert h using 1
  ext n
  rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub hg)]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

/-- The elementary identity behind the Scheffé argument. -/
theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Convergence in `L¹` together with convergence of second moments implies
convergence in `L¹` of the squares. No finite-measure or sign assumption is used. -/
theorem tendsto_integral_abs_sq_sub_of_l1_of_moments
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hf2 : ∀ n, Integrable (fun ω ↦ (f n ω) ^ 2) μ)
    (hg2 : Integrable (fun ω ↦ (g ω) ^ 2) μ)
    (hL1 : Tendsto (fun n ↦ ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n ↦ ∫ ω, (f n ω) ^ 2 ∂μ) atTop
      (𝓝 (∫ ω, (g ω) ^ 2 ∂μ))) :
    Tendsto (fun n ↦ ∫ ω, |(f n ω) ^ 2 - (g ω) ^ 2| ∂μ) atTop (𝓝 0) := by
  have hm := tendstoInMeasure_of_integral_abs_sub hf hg hL1
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, hms, hae⟩ := (hm.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hmin_int (k : ℕ) :
      Integrable (fun ω ↦ min ((f (ns (ms k)) ω) ^ 2) ((g ω) ^ 2)) μ :=
    (hf2 (ns (ms k))).inf hg2
  have hmin : Tendsto
      (fun k ↦ ∫ ω, min ((f (ns (ms k)) ω) ^ 2) ((g ω) ^ 2) ∂μ) atTop
      (𝓝 (∫ ω, (g ω) ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω ↦ (g ω) ^ 2)
      (fun k ↦ (hmin_int k).aestronglyMeasurable) hg2
    · intro k
      exact Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
        exact min_le_right _ _
    · filter_upwards [hae] with ω hω
      simpa using (hω.pow 2).min
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (g ω) ^ 2) atTop (𝓝 ((g ω) ^ 2)))
  have hmom := (h2.comp hns).comp hms.tendsto_atTop
  have hcomb := (hmom.add_const (∫ ω, (g ω) ^ 2 ∂μ)).sub (hmin.const_mul 2)
  have heq (k : ℕ) :
      (∫ ω, |(f (ns (ms k)) ω) ^ 2 - (g ω) ^ 2| ∂μ) =
        (∫ ω, (f (ns (ms k)) ω) ^ 2 ∂μ) + (∫ ω, (g ω) ^ 2 ∂μ) -
          2 * (∫ ω, min ((f (ns (ms k)) ω) ^ 2) ((g ω) ^ 2) ∂μ) := by
    simp_rw [abs_sub_eq_add_sub_two_min]
    have hsum : Integrable (fun ω ↦ (f (ns (ms k)) ω) ^ 2 + (g ω) ^ 2) μ :=
      (hf2 (ns (ms k))).add hg2
    rw [integral_sub hsum ((hmin_int k).const_mul 2),
      integral_add (hf2 (ns (ms k))) hg2, integral_const_mul]
  simp only [Function.comp_apply] at hcomb
  have hzero : (∫ ω, (g ω) ^ 2 ∂μ) + (∫ ω, (g ω) ^ 2 ∂μ) -
      2 * (∫ ω, (g ω) ^ 2 ∂μ) = 0 := by ring
  rw [hzero] at hcomb
  exact hcomb.congr' (Eventually.of_forall fun k ↦ (heq k).symm)

/-- The square-integral formulation and the `L¹`-of-squares formulation are
equivalent under genuine `L¹` convergence of the original profiles. -/
theorem tendsto_second_moments_iff_l1_squares
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hf2 : ∀ n, Integrable (fun ω ↦ (f n ω) ^ 2) μ)
    (hg2 : Integrable (fun ω ↦ (g ω) ^ 2) μ)
    (hL1 : Tendsto (fun n ↦ ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, (f n ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (g ω) ^ 2 ∂μ)) ↔
      Tendsto (fun n ↦ ∫ ω, |(f n ω) ^ 2 - (g ω) ^ 2| ∂μ) atTop (𝓝 0) := by
  constructor
  · exact tendsto_integral_abs_sq_sub_of_l1_of_moments hf hg hf2 hg2 hL1
  · intro h
    simpa using tendsto_setIntegral_of_l1 hf2 hg2 h Set.univ

end Freezing2
