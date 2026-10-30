module

public import Freezing2.Analysis.HarmonicAsymptotics
public import Freezing2.Analysis.MeshIntervals
public import Freezing2.Analysis.LocalSquareProfiles

/-!
# Uniform convergence of normalized harmonic prefixes

The floor profile integrates the zero-based sum. The paper uses the one-based
sum, whose exact endpoint correction is bounded by `n^α/n`. Thus global `L¹`
convergence controls every prefix simultaneously, including both boundary phases.
The limiting primitive is extended continuously outside the unit interval by
integrating the zero extension of its integrable profile.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The continuous extension of the limiting half-reciprocal primitive. -/
noncomputable def profilePrimitive (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..t, (Icc (0 : ℝ) 1).indicator g s) / 2

theorem continuous_profilePrimitive {g : ℝ → ℝ} (hg : Integrable g profileMeasure) :
    Continuous (profilePrimitive g) := by
  have he : Integrable ((Icc (0 : ℝ) 1).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg
  exact (he.continuous_primitive 0).div_const 2

/-- On the source domain the extension is exactly its displayed primitive. -/
theorem profilePrimitive_eq_setIntegral (g : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    profilePrimitive g t = (∫ s in Icc (0 : ℝ) t, g s) / 2 := by
  rw [profilePrimitive, intervalIntegral.integral_of_le ht0, ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  exact Set.indicator_of_mem (show s ∈ Icc (0 : ℝ) 1 from ⟨hs.1, hs.2.trans ht1⟩) g

/-- The exact normalization and one-based harmonic prefix in the source. -/
noncomputable def normalizedHarmonicPrefix (x : ℕ → ℕ → ℤ) (α : ℝ) (n b : ℕ) : ℝ :=
  (n : ℝ) ^ (α - 1) * harmonicInterval (x n) 0 b / 2

theorem normalizedHarmonicPrefix_eq (x : ℕ → ℕ → ℤ) (α : ℝ) {n : ℕ}
    (hn : 0 < n) (b : ℕ) :
    normalizedHarmonicPrefix x α n b = ((n : ℝ) ^ α / n) *
      (∑ i ∈ Finset.range b, (activeCount (x n) (i + 1) : ℝ)⁻¹) / 2 := by
  simp only [normalizedHarmonicPrefix, harmonicInterval, zero_add]
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]

/-- Every initial mesh interval integrates its zero-based population prefix. -/
theorem integral_reciprocalProfile_prefix (x : ℕ → ℕ → ℤ) (α : ℝ) {n : ℕ}
    (hn : 0 < n) (b : ℕ) :
    (∫ t in Icc (0 : ℝ) ((b : ℝ) / n), reciprocalProfile x α n t) =
      ((n : ℝ) ^ α / n) * ∑ i ∈ Finset.range b, (activeCount (x n) i : ℝ)⁻¹ := by
  have h := integral_stepProfile_meshInterval
    (fun i ↦ (n : ℝ) ^ α / (activeCount (x n) i : ℝ)) hn 0 b
  simp only [Nat.cast_zero, zero_div, ← Finset.range_eq_Ico] at h
  change (∫ t in Icc (0 : ℝ) ((b : ℝ) / n),
    stepProfile (fun i ↦ (n : ℝ) ^ α / (activeCount (x n) i : ℝ)) n t) = _
  rw [h]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

/-- The uniform error bound contains the genuine global `L¹` error and the
vanishing one-based endpoint correction. -/
noncomputable def branchPrimitiveError (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((∫ t, |reciprocalProfile x α n t - g t| ∂profileMeasure) + (n : ℝ) ^ α / n) / 2

theorem branchPrimitiveError_nonneg (x : ℕ → ℕ → ℤ) (α : ℝ) (g : ℝ → ℝ) (n : ℕ) :
    0 ≤ branchPrimitiveError x α g n := by
  apply div_nonneg _ (by norm_num)
  exact add_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) (by positivity)

theorem tendsto_branchPrimitiveError {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g) :
    Tendsto (branchPrimitiveError x α g) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α / n) atTop (𝓝 0) := by
    simpa using tendsto_profile_spike_bound hα (by norm_num : (0 : ℝ) < 2)
  unfold branchPrimitiveError
  simpa only [zero_add, zero_div] using (hL1.2.add hc).div_const 2

/-- Uniform primitive convergence at every admissible integer prefix. -/
theorem normalizedHarmonicPrefix_error_le {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n b : ℕ}
    (hn : 0 < n) (hb : b ≤ n) :
    |normalizedHarmonicPrefix x α n b - profilePrimitive g ((b : ℝ) / n)| ≤
      branchPrimitiveError x α g n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : 0 ≤ (b : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hnp.le
  have hb1 : (b : ℝ) / n ≤ 1 := (div_le_one hnp).mpr (by exact_mod_cast hb)
  have hs1 : (1 : ℝ) ≤ activeCount (x n) b := by
    have hs := (hx n).2 b hb
    have hs' : (1 : ℤ) ≤ activeCount (x n) b := by omega
    exact_mod_cast hs'
  have hi0 : 0 ≤ (activeCount (x n) b : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : (activeCount (x n) b : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hs1
  have hc : 0 ≤ (n : ℝ) ^ α / n := by positivity
  have hend : |((n : ℝ) ^ α / n) *
      (∑ i ∈ Finset.range b, (activeCount (x n) (i + 1) : ℝ)⁻¹) -
      ∫ t in Icc (0 : ℝ) ((b : ℝ) / n), reciprocalProfile x α n t| ≤ (n : ℝ) ^ α / n := by
    rw [integral_reciprocalProfile_prefix x α hn,
      sum_range_shift_eq (fun i ↦ (activeCount (x n) i : ℝ)⁻¹) b]
    simp only [activeCount_zero, Int.cast_one, inv_one]
    have he : ((n : ℝ) ^ α / n) *
        ((∑ i ∈ Finset.range b, (activeCount (x n) i : ℝ)⁻¹) +
          (activeCount (x n) b : ℝ)⁻¹ - 1) -
        ((n : ℝ) ^ α / n) * (∑ i ∈ Finset.range b, (activeCount (x n) i : ℝ)⁻¹) =
        ((n : ℝ) ^ α / n) * ((activeCount (x n) b : ℝ)⁻¹ - 1) := by ring
    rw [he, abs_mul, abs_of_nonneg hc]
    have ha : |(activeCount (x n) b : ℝ)⁻¹ - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha hc
  have hlocal := abs_setIntegral_sub_le_integral_abs_sub
    (integrable_reciprocalProfile x α n) hg (Icc (0 : ℝ) ((b : ℝ) / n))
  rw [profileMeasure_restrict_Icc (by norm_num : (0 : ℝ) ≤ 0) hb1] at hlocal
  rw [normalizedHarmonicPrefix_eq x α hn, profilePrimitive_eq_setIntegral g hb0 hb1,
    ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact (abs_sub_le _ (∫ t in Icc (0 : ℝ) ((b : ℝ) / n), reciprocalProfile x α n t) _).trans
    (by linarith)

end Freezing2
