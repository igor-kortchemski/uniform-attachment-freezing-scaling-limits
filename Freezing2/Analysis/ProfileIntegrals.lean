module

public import Freezing2.Analysis.PopulationProfile
public import Freezing2.Analysis.StepProfile
public import Freezing2.Analysis.LocalL1

/-!
# Integrals of reciprocal population profiles

The floor profile has a finite range on the unit interval, so the `L¹`
hypothesis uses genuine integrable functions. Exact mesh integration also
accounts for the endpoint shift between the zero-based profile and the
one-based harmonic sum in Lemma `lem:hnalpha(iii)`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Freezing2

/-- Every reciprocal mesh profile is integrable, including the zero horizon. -/
theorem integrable_reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) :
    Integrable (reciprocalProfile x α n) profileMeasure := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold reciprocalProfile
    simp only [Nat.cast_zero, zero_mul, Nat.floor_zero, activeCount_zero, Int.cast_one, div_one]
    exact integrable_const _
  · exact integrableOn_stepProfile_Icc
      (fun i ↦ (n : ℝ) ^ α / (activeCount (x n) i : ℝ)) hn

/-- Survival gives strictly positive real population at every time in the horizon. -/
theorem activeCount_real_pos {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    (n : ℕ) {i : ℕ} (hi : i ≤ n) : 0 < (activeCount (x n) i : ℝ) := by
  exact_mod_cast (hx n).2 i hi

/-- The floor profile is nonnegative throughout its actual integration domain. -/
theorem reciprocalProfile_nonneg {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    (α : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ reciprocalProfile x α n t := by
  have hi : ⌊(n : ℝ) * t⌋₊ ≤ n := by
    calc
      _ ≤ ⌊(n : ℝ) * 1⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n))
      _ = n := by simp
  exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α) (activeCount_real_pos hx n hi).le

/-- Almost-everywhere form of positivity, with the endpoints retained. -/
theorem reciprocalProfile_nonneg_ae {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    (α : ℝ) (n : ℕ) : ∀ᵐ t ∂profileMeasure, 0 ≤ reciprocalProfile x α n t := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact reciprocalProfile_nonneg hx α n ht

/-- Exact integral formula for the source's zero-based mesh profile. -/
theorem integral_reciprocalProfile (x : ℕ → ℕ → ℤ) (α : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ t, reciprocalProfile x α n t ∂profileMeasure) =
      ((n : ℝ) ^ α / n) * ∑ i ∈ Finset.range n, (activeCount (x n) i : ℝ)⁻¹ := by
  change (∫ t in Icc (0 : ℝ) 1,
    stepProfile (fun i ↦ (n : ℝ) ^ α / (activeCount (x n) i : ℝ)) n t) = _
  rw [integral_stepProfile_Icc _ hn]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

/-- The one-based harmonic sum denoted `h_n` in the manuscript. -/
noncomputable def harmonicTotal (x : ℕ → ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (activeCount (x n) (i + 1) : ℝ)⁻¹

/-- Changing from the floor profile to the source's one-based sum produces
exactly the endpoint correction; neither endpoint is silently dropped. -/
theorem harmonicTotal_profile_difference (x : ℕ → ℕ → ℤ) (α : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ α / n) * harmonicTotal x n -
      (∫ t, reciprocalProfile x α n t ∂profileMeasure) =
      ((n : ℝ) ^ α / n) * ((activeCount (x n) n : ℝ)⁻¹ - 1) := by
  rw [integral_reciprocalProfile x α hn, harmonicTotal,
    sum_range_shift_eq (fun i ↦ (activeCount (x n) i : ℝ)⁻¹) n]
  simp only [activeCount_zero, Int.cast_one, inv_one]
  ring

/-- The endpoint correction is bounded by the vanishing normalization. -/
theorem abs_harmonicTotal_profile_difference {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) (α : ℝ) {n : ℕ} (hn : 0 < n) :
    |((n : ℝ) ^ α / n) * harmonicTotal x n -
      (∫ t, reciprocalProfile x α n t ∂profileMeasure)| ≤ (n : ℝ) ^ α / n := by
  have hs1 : (1 : ℝ) ≤ activeCount (x n) n := by
    have hs := (hx n).2 n le_rfl
    have hs' : (1 : ℤ) ≤ activeCount (x n) n := by omega
    exact_mod_cast hs'
  have hi0 : 0 ≤ (activeCount (x n) n : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : (activeCount (x n) n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hs1
  have hc : 0 ≤ (n : ℝ) ^ α / n := by positivity
  rw [harmonicTotal_profile_difference x α hn, abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ ((n : ℝ) ^ α / n) * 1 := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [abs_le]
      constructor <;> linarith
    _ = _ := mul_one _

/-- The second convergence of `hnalpha(iii)`, with the exact mesh shift proved.
Only the `L¹` condition and `α < 1` are needed for this part of the lemma. -/
theorem tendsto_normalized_harmonicTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * harmonicTotal x n) atTop
      (𝓝 (∫ t, g t ∂profileMeasure)) := by
  have hI : Tendsto (fun n : ℕ ↦ ∫ t, reciprocalProfile x α n t ∂profileMeasure) atTop
      (𝓝 (∫ t, g t ∂profileMeasure)) := by
    simpa using tendsto_setIntegral_of_l1 (fun n : ℕ ↦ integrable_reciprocalProfile x α n)
      hL1.1 hL1.2 Set.univ
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α / n) atTop (𝓝 0) := by
    simpa using tendsto_profile_spike_bound hα (by norm_num : (0 : ℝ) < 2)
  have hd : Tendsto (fun n : ℕ ↦ |((n : ℝ) ^ α / n) * harmonicTotal x n -
      (∫ t, reciprocalProfile x α n t ∂profileMeasure)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n : ℕ ↦ abs_nonneg _) _ hc
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact abs_harmonicTotal_profile_difference hx α hn
  have hd' : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * harmonicTotal x n -
      (∫ t, reciprocalProfile x α n t ∂profileMeasure)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hd
  convert hd'.add hI using 1 <;> simp

end Freezing2
