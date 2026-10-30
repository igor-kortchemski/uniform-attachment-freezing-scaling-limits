module

public import Freezing2.Analysis.HarmonicConclusions

/-!
# Deterministic normalization for the main height theorem

The harmonic up-step scale is asymptotic to `n^(1-α)` times the strictly
positive constant `(∫g)/2`. In particular `log(n)/h_n⁺` tends to zero, the
condition needed to apply the companion paper's height concentration theorem.
Only the global reciprocal L¹ hypothesis is needed for these conclusions.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- The limiting constant in the main height theorem is strictly positive. -/
theorem harmonicUp_limit_pos {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    0 < (∫ t, g t ∂profileMeasure) / 2 :=
  div_pos (reciprocalProfile_integral_pos hL1 hpos) (by norm_num)

/-- The up-step scale converges after multiplication by `n^α/n`. -/
theorem tendsto_scaled_harmonicUpTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * harmonicUpTotal x n) atTop
      (𝓝 ((∫ t, g t ∂profileMeasure) / 2)) := by
  have h := (tendsto_normalized_harmonicUpTotal hx hα0 hα1 hL1
    (hpos.mono fun _ ht ↦ ht.le)).div_const 2
  convert h using 1
  ext n
  ring

/-- The harmonic up-step scale is eventually positive, so its later use as a
normalizing denominator does not rely on totalized division at zero. -/
theorem eventually_harmonicUpTotal_pos {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    ∀ᶠ n in atTop, 0 < harmonicUpTotal x n := by
  have h := (tendsto_scaled_harmonicUpTotal hx hα0 hα1 hL1 hpos).eventually_const_lt
    (harmonicUp_limit_pos hL1 hpos)
  filter_upwards [h] with n hn
  by_contra! hnot
  exact (not_le_of_gt hn) (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnot)

theorem eventually_harmonicUpTotal_ne_zero {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    ∀ᶠ n in atTop, harmonicUpTotal x n ≠ 0 :=
  (eventually_harmonicUpTotal_pos hx hα0 hα1 hL1 hpos).mono fun _ hn ↦ ne_of_gt hn

/-- The logarithm is negligible at every positive polynomial height scale. -/
theorem tendsto_normalized_log {α : ℝ} (hα : α < 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * Real.log n) atTop (𝓝 0) := by
  have hlow : ∀ᶠ n : ℕ in atTop, 0 ≤ ((n : ℝ) ^ α / n) * Real.log n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))
  have hupp : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ α / n) * Real.log n ≤
        ((n : ℝ) ^ α / n) * (1 + Real.log (n + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlog := Real.log_le_log hn' (show (n : ℝ) ≤ n + 1 by linarith)
    linarith
  exact squeeze_zero' hlow hupp (tendsto_normalized_log_endpoint hα)

/-- The condition `log(n) = o(h_n⁺)` needed for the companion height result
follows from the source's reciprocal-profile assumption. -/
theorem tendsto_log_div_harmonicUpTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ ↦ Real.log n / harmonicUpTotal x n) atTop (𝓝 0) := by
  have h := (tendsto_normalized_log hα1).div
    (tendsto_scaled_harmonicUpTotal hx hα0 hα1 hL1 hpos)
    (ne_of_gt (harmonicUp_limit_pos hL1 hpos))
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_div_mul_left _ _ (ne_of_gt (div_pos (Real.rpow_pos_of_pos hn' α) hn'))

/-- The same limit with the main theorem's denominator `n^(1-α)`. -/
theorem tendsto_harmonicUpTotal_div_rpow {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n : ℕ ↦ harmonicUpTotal x n / (n : ℝ) ^ (1 - α)) atTop
      (𝓝 ((∫ t, g t ∂profileMeasure) / 2)) := by
  apply (tendsto_scaled_harmonicUpTotal hx hα0 hα1 hL1 hpos).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one,
    div_div_eq_mul_div]
  ring

end Freezing2
