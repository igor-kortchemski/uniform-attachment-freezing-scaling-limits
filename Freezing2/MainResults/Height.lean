module

public import Freezing2.Probability.CompanionModel
public import Freezing2.Analysis.HeightNormalization
public import Freezing2.Analysis.LpScaling
public import Freezing2.Analysis.SourceHypotheses

/-!
# The main height scaling limit

This is Introduction Theorem `thm:heightalpha`. The random tree has the actual
uniform-attachment/freezing law of Algorithm 1, and its height is the maximum
root distance in the finite tree. The companion maximum-height result is
proved in the vendored dependency closure; it is not an assumed concentration
estimate. Its logarithmic-scale hypothesis follows from the reciprocal-profile
limit proved in this project.

Only the source's global L¹ condition is needed for this theorem. The local
square-moment hypothesis is not used. The companion proof uses forward MGFs
instead of the paper's reverse Bernoulli representation; equality of the two
tree constructions remains a separate obligation.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ENNReal

namespace Freezing2

/-- The main height limit, for a general positive limiting reciprocal profile.
All finite real exponents `p ≥ 1` and the varying tree laws are retained. -/
theorem height_scaling_limit {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun s : Freezing1.Forward.State ↦
        (Freezing1.Forward.treeHeight s : ℝ) / (n : ℝ) ^ (1 - α) -
          (∫ t, g t ∂profileMeasure) / 2)
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  have hτ (n : ℕ) :
      (n : ℕ∞) < Freezing1.extinctionTime (companionSchedule (x n)) :=
    companion_before_extinction (x n) (hx n).1 (hx n).2
  have hscale (n : ℕ) : Freezing1.heightScale (companionSchedule (x n)) n =
      harmonicUpTotal x n := companion_heightScale (x n) (hx n).1 n
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n /
      Freezing1.heightScale (companionSchedule (x n)) n) atTop (𝓝 0) := by
    simp_rw [hscale]
    exact tendsto_log_div_harmonicUpTotal hx hα0 hα1 hL1 hpos
  have hheight := Freezing1.maximum_height_tendsto_Lp
    (fun n ↦ companionSchedule (x n)) hτ hlog hp
  simp_rw [hscale] at hheight
  apply tendsto_eLpNorm_change_normalization
    (μ := fun n ↦ freezingTreeLaw x n)
    (Z := fun _ s ↦ (Freezing1.Forward.treeHeight s : ℝ))
    (a := harmonicUpTotal x) (s := fun n : ℕ ↦ (n : ℝ) ^ (1 - α))
    (by simpa using ENNReal.ofReal_le_ofReal hp)
    (eventually_harmonicUpTotal_ne_zero hx hα0 hα1 hL1 hpos)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hn : (0 : ℝ) < n) _)
  · exact tendsto_harmonicUpTotal_div_rpow hx hα0 hα1 hL1 hpos
  · exact hheight

/-- The limiting height constant in the exact integrand printed in the paper. -/
theorem reciprocal_half_integral (f : ℝ → ℝ) :
    (∫ t, 1 / f t ∂profileMeasure) / 2 =
      ∫ t in Set.Icc (0 : ℝ) 1, 1 / (2 * f t) := by
  change (∫ t, 1 / f t ∂profileMeasure) / 2 = ∫ t, 1 / (2 * f t) ∂profileMeasure
  rw [← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun t ↦ by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

/-- Introduction Theorem `thm:heightalpha` in the source's `f` notation.
The result holds under a weaker set of premises: local L² is unnecessary. -/
theorem height_scaling_limit_source {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun s : Freezing1.Forward.State ↦
        (Freezing1.Forward.treeHeight s : ℝ) / (n : ℝ) ^ (1 - α) -
          ∫ t in Set.Icc (0 : ℝ) 1, 1 / (2 * f t))
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  simpa only [reciprocal_half_integral] using
    height_scaling_limit hx hα0 hα1 hL1 (positiveProfile_reciprocal hf) hp

/-- The source array starts at positive horizons. Extending its unused zero row
does not change the claimed tree-height limit under the original tree laws. -/
theorem height_scaling_limit_positive_horizons {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ ↦ eLpNorm
      (fun s : Freezing1.Forward.State ↦
        (Freezing1.Forward.treeHeight s : ℝ) / (n : ℝ) ^ (1 - α) -
          ∫ t in Set.Icc (0 : ℝ) 1, 1 / (2 * f t))
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  apply (height_scaling_limit_source (admissible_initialRowExtension hx)
    hα0 hα1 hf (hasL1ReciprocalProfile_initialRowExtension hL1) hp).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [freezingTreeLaw, hn]

end Freezing2
