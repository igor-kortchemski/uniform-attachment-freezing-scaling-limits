module

public import Freezing2.Analysis.HarmonicAsymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# The harmonic conclusions in the manuscript's normalization

This module gives the finite maximum in `lem:hnalpha(iv)` and the asymptotic
equivalences in part (iii). Invalid endpoint pairs contribute zero to the finite
maximum, which extends it to horizon zero without changing any positive-horizon
maximum. Every valid pair is the inclusive interval `1 ≤ a ≤ b ≤ n`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology Asymptotics

namespace Freezing2

/-- The maximum harmonic deviation over all inclusive subintervals of `[1,n]`. -/
noncomputable def harmonicDeviationMax (x : ℕ → ℕ → ℤ) (n : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).sup' Finset.univ_nonempty
    (fun p ↦ if 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val then
      |harmonicUpInterval (x n) (p.1.val - 1) (p.2.val + 1 - p.1.val) -
        harmonicInterval (x n) (p.1.val - 1) (p.2.val + 1 - p.1.val) / 2|
      else 0)

theorem harmonicDeviationMax_nonneg (x : ℕ → ℕ → ℤ) (n : ℕ) :
    0 ≤ harmonicDeviationMax x n := by
  unfold harmonicDeviationMax
  rw [Finset.le_sup'_iff]
  refine ⟨((0, 0) : Fin (n + 1) × Fin (n + 1)), Finset.mem_univ _, ?_⟩
  norm_num

theorem harmonicDeviationMax_le {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) (n : ℕ) :
    harmonicDeviationMax x n ≤ reciprocalErrorTotal x n / 2 + (1 + Real.log (n + 1)) := by
  unfold harmonicDeviationMax
  apply Finset.sup'_le
  intro p _
  split_ifs with hp
  · apply harmonicInterval_deviation_bound hx
    have := p.2.isLt
    omega
  · have he : 0 ≤ reciprocalErrorTotal x n := by
      exact Finset.sum_nonneg fun i hi ↦ reciprocalErrorAt_nonneg (hx n).2
        (by have := Finset.mem_range.mp hi; omega)
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ n + 1 by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    linarith

/-- Lemma `hnalpha(iv)` with its maximum and its original normalization. -/
theorem tendsto_harmonicDeviationMax {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ harmonicDeviationMax x n / (n : ℝ) ^ (1 - α))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * harmonicDeviationMax x n)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ mul_nonneg (by positivity) (harmonicDeviationMax_nonneg x n))
      (fun n ↦ mul_le_mul_of_nonneg_left (harmonicDeviationMax_le hx n) (by positivity))
      (tendsto_harmonicDeviation_bound hx hα0 hα1 hL1 hg)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one, div_div_eq_mul_div]
  ring

/-- Positivity of the limiting harmonic integral, needed for the source's `∼`. -/
theorem reciprocalProfile_integral_pos {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    0 < ∫ t, g t ∂profileMeasure := by
  apply integral_pos_of_ae_pos hL1.1 hpos
  simp [profileMeasure, Measure.restrict_eq_zero, Real.volume_Icc]

/-- The harmonic sum is asymptotic to the positive limiting integral. -/
theorem harmonicTotal_asymptotic {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n) ~[atTop]
      (fun _ ↦ ∫ t, g t ∂profileMeasure) := by
  apply (Asymptotics.isEquivalent_const_iff_tendsto
    (ne_of_gt (reciprocalProfile_integral_pos hL1 hpos))).mpr
  apply (tendsto_normalized_harmonicTotal hx hα1 hL1).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]

/-- The two equivalences in `hnalpha(iii)`, with no zero-limit exception hidden. -/
theorem harmonicUpTotal_asymptotic {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    (fun n : ℕ ↦ 2 * (n : ℝ) ^ (α - 1) * harmonicUpTotal x n) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n) := by
  have hup : (fun n : ℕ ↦ 2 * (n : ℝ) ^ (α - 1) * harmonicUpTotal x n) ~[atTop]
      (fun _ ↦ ∫ t, g t ∂profileMeasure) := by
    apply (Asymptotics.isEquivalent_const_iff_tendsto
      (ne_of_gt (reciprocalProfile_integral_pos hL1 hpos))).mpr
    apply (tendsto_normalized_harmonicUpTotal hx hα0 hα1 hL1
      (hpos.mono fun _ h ↦ h.le)).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]
  exact hup.trans (harmonicTotal_asymptotic hx hα1 hL1 hpos).symm

end Freezing2
