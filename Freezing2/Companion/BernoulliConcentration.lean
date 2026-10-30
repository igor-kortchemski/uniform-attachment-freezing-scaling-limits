module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.RateFunction
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Bennett bounds for a sum of independent Bernoulli variables

This module proves Proposition `prop:bennett` of *Uniform attachment with
freezing*. A Bernoulli variable is specified by its law, with mass `p` at one
and `1-p` at zero. The proof uses Mathlib's Chernoff inequality and derives the
moment-generating-function estimate from that law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exact moment generating function of a Bernoulli variable. -/
theorem mgf_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    mgf Y μ θ = (p : ℝ) * Real.exp θ + (1 - (p : ℝ)) := by
  calc
    mgf Y μ θ = ∫ x : ℝ, Real.exp (θ * x) ∂bernoulliMeasure 1 0 p := by
      exact hY.integral_comp (f := fun x : ℝ ↦ Real.exp (θ * x)) (by fun_prop)
    _ = (p : ℝ) * Real.exp θ + (1 - (p : ℝ)) := by
      rw [integral_bernoulliMeasure]
      simp

theorem integrable_exp_mul_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    Integrable (fun ω ↦ Real.exp (θ * Y ω)) μ :=
  hY.integrable_fun_comp
    (integrable_bernoulliMeasure 1 0 p (fun x : ℝ ↦ Real.exp (θ * x)))

/-- Exponential upper bound obtained from `1 + z ≤ exp z`. -/
theorem mgf_bernoulli_le {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    mgf Y μ θ ≤ Real.exp ((p : ℝ) * (Real.exp θ - 1)) := by
  rw [mgf_bernoulli hY]
  have h := Real.add_one_le_exp ((p : ℝ) * (Real.exp θ - 1))
  linarith

/-- The MGF bound for a finite sum, with its mean derived from the Bernoulli parameters. -/
theorem mgf_sum_bernoulli_le {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (θ : ℝ) :
    mgf (∑ i ∈ s, Y i) μ θ ≤
      Real.exp ((∑ i ∈ s, (p i : ℝ)) * (Real.exp θ - 1)) := by
  rw [h_indep.mgf_sum hY]
  calc
    ∏ i ∈ s, mgf (Y i) μ θ ≤ ∏ i ∈ s, Real.exp ((p i : ℝ) * (Real.exp θ - 1)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        exact mgf_bernoulli_le (hLaw i) θ
    _ = Real.exp (∑ i ∈ s, (p i : ℝ) * (Real.exp θ - 1)) := (Real.exp_sum s _).symm
    _ = Real.exp ((∑ i ∈ s, (p i : ℝ)) * (Real.exp θ - 1)) := by
      rw [Finset.sum_mul]

/-- The negative-parameter centered rate is bounded by the positive-parameter rate. -/
theorem exp_neg_sub_one_add_le {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.exp (-θ) - 1 + θ ≤ Real.exp θ - 1 - θ := by
  have h := Real.self_le_sinh_iff.mpr hθ
  rw [Real.sinh_eq] at h
  linarith

/-- Chernoff's optimizing parameter gives the Bennett rate exactly. -/
theorem bennett_exponent_identity {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    -Real.log (1 + t / m) * (m + t) + m * (Real.exp (Real.log (1 + t / m)) - 1) =
      -m * bennettRate (t / m) := by
  have hpos : 0 < 1 + t / m := by positivity
  rw [Real.exp_log hpos]
  unfold bennettRate
  field_simp [hm.ne']
  ring

/-- Bennett's upper-tail bound. Measurability is the usual random-variable typing condition. -/
theorem bernoulli_sum_upper_tail [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < ∑ i ∈ s, Y i ω} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by
    have hd : 0 < t / m := div_pos ht hm
    linarith)
  have h_int : Integrable (fun ω ↦ Real.exp (θ * (∑ i ∈ s, Y i) ω)) μ :=
    h_indep.integrable_exp_mul_sum hY (fun i _ ↦ integrable_exp_mul_bernoulli (hLaw i) θ)
  calc
    μ.real {ω | m + t < ∑ i ∈ s, Y i ω} ≤ μ.real {ω | m + t ≤ (∑ i ∈ s, Y i) ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      change m + t < ∑ i ∈ s, Y i ω at hω
      change m + t ≤ (∑ i ∈ s, Y i) ω
      simpa only [Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-θ * (m + t)) * mgf (∑ i ∈ s, Y i) μ θ :=
      measure_ge_le_exp_mul_mgf (m + t) hθ h_int
    _ ≤ Real.exp (-θ * (m + t)) * Real.exp (m * (Real.exp θ - 1)) := by
      apply mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le hY h_indep hLaw s θ)
      exact (Real.exp_pos _).le
    _ = Real.exp (-m * bennettRate (t / m)) := by
      rw [← Real.exp_add]
      congr 1
      exact bennett_exponent_identity hm ht

/-- Bennett's lower-tail bound with the same rate as the upper tail. -/
theorem bernoulli_sum_lower_tail [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, Y i ω) < (∑ i ∈ s, (p i : ℝ)) - t} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by
    have hd : 0 < t / m := div_pos ht hm
    linarith)
  have h_int : Integrable (fun ω ↦ Real.exp ((-θ) * (∑ i ∈ s, Y i) ω)) μ :=
    h_indep.integrable_exp_mul_sum hY (fun i _ ↦ integrable_exp_mul_bernoulli (hLaw i) (-θ))
  calc
    μ.real {ω | (∑ i ∈ s, Y i ω) < m - t} ≤ μ.real {ω | (∑ i ∈ s, Y i) ω ≤ m - t} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      change (∑ i ∈ s, Y i ω) < m - t at hω
      change (∑ i ∈ s, Y i) ω ≤ m - t
      simpa only [Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-(-θ) * (m - t)) * mgf (∑ i ∈ s, Y i) μ (-θ) :=
      measure_le_le_exp_mul_mgf (m - t) (neg_nonpos.mpr hθ) h_int
    _ ≤ Real.exp (-(-θ) * (m - t)) * Real.exp (m * (Real.exp (-θ) - 1)) := by
      apply mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le hY h_indep hLaw s (-θ))
      exact (Real.exp_pos _).le
    _ = Real.exp (-(-θ) * (m - t) + m * (Real.exp (-θ) - 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le hθ) hm.le
      nlinarith
    _ = Real.exp (-m * bennettRate (t / m)) := by
      congr 1
      exact bennett_exponent_identity hm ht

end Freezing1
