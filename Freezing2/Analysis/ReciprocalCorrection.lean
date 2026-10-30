module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Vanishing reciprocal corrections under L¹ convergence

For nonnegative `gₙ` converging to `g` in L¹ and positive `cₙ → ∞`, the integral
of `gₙ² / (cₙ + gₙ)` tends to zero. This is the analytic mechanism behind
equation `eq:lemme hnalpha convergence somme vers 0` in the source.

The proof uses a scalar contraction estimate and dominated convergence in place
of the manuscript's uniform-integrability argument. It works for an arbitrary
measure when the limiting function is integrable.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- The correction map used when replacing `1/(S+1)` by `1/S`. -/
noncomputable def reciprocalCorrection (c u : ℝ) : ℝ := u ^ 2 / (c + u)

theorem reciprocalCorrection_nonneg {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    0 ≤ reciprocalCorrection c u := by
  unfold reciprocalCorrection
  positivity

theorem reciprocalCorrection_le {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    reciprocalCorrection c u ≤ u := by
  unfold reciprocalCorrection
  apply (div_le_iff₀ (show 0 < c + u by linarith)).mpr
  nlinarith [mul_nonneg hc.le hu]

/-- The correction maps have Lipschitz constant one on the nonnegative half-line,
uniformly in the positive parameter `c`. -/
theorem reciprocalCorrection_abs_sub_le {c u v : ℝ}
    (hc : 0 < c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |reciprocalCorrection c u - reciprocalCorrection c v| ≤ |u - v| := by
  have hcu : 0 < c + u := by linarith
  have hcv : 0 < c + v := by linarith
  have hd : 0 < (c + u) * (c + v) := mul_pos hcu hcv
  have hsmall : c ^ 2 ≤ (c + u) * (c + v) := by
    nlinarith [mul_nonneg hc.le hu, mul_nonneg hc.le hv, mul_nonneg hu hv]
  have hratio : c ^ 2 / ((c + u) * (c + v)) ≤ 1 :=
    (div_le_one hd).mpr hsmall
  have hratio0 : 0 ≤ c ^ 2 / ((c + u) * (c + v)) := by positivity
  have hid : reciprocalCorrection c u - reciprocalCorrection c v =
      (u - v) * (1 - c ^ 2 / ((c + u) * (c + v))) := by
    unfold reciprocalCorrection
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg (sub_nonneg.mpr hratio)]
  calc
    _ ≤ |u - v| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |u - v| := mul_one _

theorem reciprocalCorrection_le_abs_sub_add {c u v : ℝ}
    (hc : 0 < c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    reciprocalCorrection c u ≤ |u - v| + reciprocalCorrection c v := by
  have h := reciprocalCorrection_abs_sub_le hc hu hv
  have h' := le_abs_self (reciprocalCorrection c u - reciprocalCorrection c v)
  linarith

/-- For a fixed input the correction vanishes as the parameter diverges. -/
theorem tendsto_reciprocalCorrection {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (u : ℝ) :
    Tendsto (fun n ↦ reciprocalCorrection (c n) u) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop u hc)

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aestronglyMeasurable_reciprocalCorrection {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (c : ℝ) :
    AEStronglyMeasurable (fun ω ↦ reciprocalCorrection c (f ω)) μ := by
  have hf' := hf.aemeasurable
  unfold reciprocalCorrection
  exact ((hf'.pow_const 2).div (aemeasurable_const.add hf')).aestronglyMeasurable

/-- The correction is integrable, with no square-integrability requirement. -/
theorem integrable_reciprocalCorrection {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ω ↦ reciprocalCorrection c (f ω)) μ := by
  apply hf.mono' (aestronglyMeasurable_reciprocalCorrection hf.aestronglyMeasurable c)
  filter_upwards [hf0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalCorrection_nonneg hc hω)]
  exact reciprocalCorrection_le hc hω

/-- Dominated convergence for a fixed nonnegative integrable function. -/
theorem tendsto_integral_reciprocalCorrection_fixed {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) {c : ℕ → ℝ} (hc0 : ∀ n, 0 < c n)
    (hc : Tendsto c atTop atTop) :
    Tendsto (fun n ↦ ∫ ω, reciprocalCorrection (c n) (f ω) ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω ↦ reciprocalCorrection (c n) (f ω)) (f := fun _ ↦ (0 : ℝ)) f
    (fun n ↦ aestronglyMeasurable_reciprocalCorrection hf.aestronglyMeasurable (c n)) hf
    (fun n ↦ ?_) (Filter.Eventually.of_forall fun ω ↦ tendsto_reciprocalCorrection hc (f ω))
  · simpa using h
  · filter_upwards [hf0] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalCorrection_nonneg (hc0 n) hω)]
    exact reciprocalCorrection_le (hc0 n) hω

/-- Abstract L¹ transfer for the correction in equation
`eq:lemme hnalpha convergence somme vers 0`. The only convergence assumption on
`fₙ` is convergence to `f` of the integral of its absolute difference. -/
theorem tendsto_integral_reciprocalCorrection_of_l1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hf0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    {c : ℕ → ℝ} (hc0 : ∀ n, 0 < c n) (hc : Tendsto c atTop atTop)
    (hfg : Tendsto (fun n ↦ ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, reciprocalCorrection (c n) (f n ω) ∂μ) atTop (𝓝 0) := by
  have hfixed := tendsto_integral_reciprocalCorrection_fixed hg hg0 hc0 hc
  have hibound (n : ℕ) :
      (∫ ω, reciprocalCorrection (c n) (f n ω) ∂μ) ≤
        (∫ ω, |f n ω - g ω| ∂μ) + (∫ ω, reciprocalCorrection (c n) (g ω) ∂μ) := by
    have hd := ((hf n).sub hg).abs
    have hi := integrable_reciprocalCorrection hg hg0 (hc0 n)
    calc
      _ ≤ ∫ ω, |f n ω - g ω| + reciprocalCorrection (c n) (g ω) ∂μ := by
        apply integral_mono_ae (integrable_reciprocalCorrection (hf n) (hf0 n) (hc0 n))
          (hd.add hi)
        filter_upwards [hf0 n, hg0] with ω hfn hgn
        exact reciprocalCorrection_le_abs_sub_add (hc0 n) hfn hgn
      _ = _ := integral_add hd hi
  apply squeeze_zero (fun n ↦ integral_nonneg_of_ae ?_) hibound
  · simpa using hfg.add hfixed
  · filter_upwards [hf0 n] with ω hω
    exact reciprocalCorrection_nonneg (hc0 n) hω

/-- Algebraic specialization to the reciprocal expression appearing in the
paper. The positivity assumptions also exclude every zero denominator. -/
theorem reciprocalCorrection_div {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    reciprocalCorrection c (c / s) = c / ((s + 1) * s) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsum : s + 1 ≠ 0 := by positivity
  unfold reciprocalCorrection
  field_simp

end Integral

end Freezing2
