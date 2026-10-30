module

public import Freezing2.Analysis.ProfileCorrection

/-!
# Uniform harmonic balance and asymptotics

The exact potential estimate and the vanishing reciprocal correction imply
the asymptotic balance of up and down steps in Lemma `lem:hnalpha(iii–iv)`.
Intervals are written `(a,a+m]`; thus the source's inclusive interval `[a,b]`
corresponds to starting time `a-1` and length `b+1-a`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Freezing2

/-- The logarithmic endpoint contribution vanishes at every sublinear scaling. -/
theorem tendsto_normalized_log_endpoint {α : ℝ} (hα : α < 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * (1 + Real.log (n + 1)))
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α / n) atTop (𝓝 0) := by
    simpa using tendsto_profile_spike_bound hα (by norm_num : (0 : ℝ) < 2)
  have hl : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 - α))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl' : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * Real.log n)
      atTop (𝓝 0) := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_sub hn', Real.rpow_one, div_div_eq_mul_div]
    ring
  have hu : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) *
      (1 + Real.log 2 + Real.log n)) atTop (𝓝 0) := by
    convert (hc.mul_const (1 + Real.log 2)).add hl' using 1
    · ext n
      ring
    · simp
  have hnonneg (n : ℕ) : 0 ≤ ((n : ℝ) ^ α / n) * (1 + Real.log (n + 1)) := by
    apply mul_nonneg (by positivity)
    have := Real.log_nonneg (show (1 : ℝ) ≤ n + 1 by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    linarith
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hu
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n + 1)
    (show (n : ℝ) + 1 ≤ 2 * n by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt hn0)] at hlog
  linarith

/-- The harmonic sum over `(a,a+m]`, with the original signed driving walk. -/
noncomputable def harmonicInterval (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, (activeCount x (a + i + 1) : ℝ)⁻¹

/-- The harmonic sum restricted to upward steps, in the source's notation. -/
noncomputable def harmonicUpInterval (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m,
    if x (a + i + 1) = 1 then (activeCount x (a + i + 1) : ℝ)⁻¹ else 0

/-- The natural-walk encoding agrees with the source's signed-step sum. -/
theorem reciprocalUpSum_eq_harmonicUpInterval (x : ℕ → ℤ) {N a m : ℕ}
    (hs : SurvivesThrough x N) (ham : a + m ≤ N) :
    reciprocalUpSum (fun i ↦ (activeCount x i).toNat) a m =
      harmonicUpInterval x a m := by
  unfold reciprocalUpSum harmonicUpInterval
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : a + i < N := by have := Finset.mem_range.mp hi; omega
  have hcast : ((activeCount x (a + i + 1)).toNat : ℝ) =
      (activeCount x (a + i + 1) : ℝ) := by
    exact_mod_cast activeCount_nat_cast x hs (by omega : a + i + 1 ≤ N)
  simp only [activeCount_nat_up_iff x hs hiN, hcast]

/-- The two signed-step contributions partition the whole harmonic sum. -/
theorem reciprocalUpSum_add_downSum (x : ℕ → ℤ) (hx : IsSigned x)
    {N a m : ℕ} (hs : SurvivesThrough x N) (ham : a + m ≤ N) :
    reciprocalUpSum (fun i ↦ (activeCount x i).toNat) a m +
      reciprocalDownSum (fun i ↦ (activeCount x i).toNat) a m =
      harmonicInterval x a m := by
  unfold reciprocalUpSum reciprocalDownSum harmonicInterval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : a + i < N := by have := Finset.mem_range.mp hi; omega
  have hcast : ((activeCount x (a + i + 1)).toNat : ℝ) =
      (activeCount x (a + i + 1) : ℝ) := by
    exact_mod_cast activeCount_nat_cast x hs (by omega : a + i + 1 ≤ N)
  simp only [activeCount_nat_up_iff x hs hiN, activeCount_nat_down_iff x hs hiN, hcast]
  rcases hx (a + i + 1) (by omega) with h | h <;> simp [h]

/-- One bound valid simultaneously for every interval in the horizon. -/
theorem harmonicInterval_deviation_bound {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) {N a m : ℕ} (ham : a + m ≤ N) :
    |harmonicUpInterval (x N) a m - harmonicInterval (x N) a m / 2| ≤
      reciprocalErrorTotal x N / 2 + (1 + Real.log (N + 1)) := by
  have hbalance := driver_reciprocal_balance_bound (x N) (hx N).1 (hx N).2 ham
  have herror := driver_reciprocalErrorSum_le_total hx ham
  have hpartition := reciprocalUpSum_add_downSum (x N) (hx N).1 (hx N).2 ham
  rw [reciprocalUpSum_eq_harmonicUpInterval (x N) (hx N).2 ham] at hbalance hpartition
  apply abs_le.mpr
  have hb := abs_le.mp hbalance
  constructor <;> linarith [hb.1, hb.2]

/-- The common normalized bound for all intervals converges to zero. -/
theorem tendsto_harmonicDeviation_bound {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) *
      (reciprocalErrorTotal x n / 2 + (1 + Real.log (n + 1)))) atTop (𝓝 0) := by
  convert ((tendsto_reciprocalErrorTotal hx hα0 hα1 hL1 hg).div_const 2).add
    (tendsto_normalized_log_endpoint hα1) using 1
  · ext n
    ring
  · simp

/-- Uniform form of `hnalpha(iv)`, including empty intervals. The quantifier
over all intervals is inside the eventual quantifier. -/
theorem eventually_uniform_harmonic_balance {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a m : ℕ, a + m ≤ n →
      ((n : ℝ) ^ α / n) *
        |harmonicUpInterval (x n) a m - harmonicInterval (x n) a m / 2| < ε := by
  have h := (tendsto_harmonicDeviation_bound hx hα0 hα1 hL1 hg).eventually_lt_const hε
  filter_upwards [h] with n hn
  intro a m ham
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (harmonicInterval_deviation_bound hx ham) (by positivity)) hn

/-- The source's `h_n⁺`. -/
noncomputable def harmonicUpTotal (x : ℕ → ℕ → ℤ) (n : ℕ) : ℝ :=
  harmonicUpInterval (x n) 0 n

/-- The up-step harmonic sum has half the limiting integral, as in `hnalpha(iii)`. -/
theorem tendsto_normalized_harmonicUpTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) ^ α / n) * harmonicUpTotal x n)
      atTop (𝓝 (∫ t, g t ∂profileMeasure)) := by
  have hd : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) *
      |harmonicUpTotal x n - harmonicTotal x n / 2|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n : ℕ ↦ by positivity) _
      (tendsto_harmonicDeviation_bound hx hα0 hα1 hL1 hg)
    intro n
    simpa [harmonicUpTotal, harmonicInterval, harmonicTotal] using
      mul_le_mul_of_nonneg_left (harmonicInterval_deviation_bound hx
        (show 0 + n ≤ n by omega)) (by positivity : 0 ≤ (n : ℝ) ^ α / n)
  have hd' : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) *
      (harmonicUpTotal x n - harmonicTotal x n / 2)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    convert hd using 1
    ext n
    simp only [Function.comp_apply, abs_mul,
      abs_of_nonneg (show 0 ≤ (n : ℝ) ^ α / n by positivity)]
  convert (hd'.const_mul 2).add (tendsto_normalized_harmonicTotal hx hα1 hL1) using 1
  · ext n
    ring
  · simp

end Freezing2
