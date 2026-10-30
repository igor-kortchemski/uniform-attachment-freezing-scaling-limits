module

public import Freezing2.Analysis.ExponentialDecay
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite triangular survival products

The logarithmic remainder is proved directly from the elementary upper and
lower logarithm inequalities. Vanishing maximal hazard and a convergent total
hazard imply the exponential survival limit, with no independence assumption.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace Freezing2

/-- A uniform second-order logarithm remainder for a small nonnegative hazard. -/
theorem abs_log_one_sub_add_le {u : ℝ} (_hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  have hp : 0 < 1 - u := by linarith
  have hupper := Real.log_le_sub_one_of_pos hp
  have hlower := Real.one_sub_inv_le_log_of_pos hp
  have hid : 1 - (1 - u)⁻¹ + u = -(u ^ 2 / (1 - u)) := by
    field_simp
    ring
  have hsq : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg u]
  rw [abs_of_nonpos (by linarith : Real.log (1 - u) + u ≤ 0)]
  linarith

/-- The aggregate logarithmic error is bounded by maximum hazard times total
hazard. Empty products and empty sums are included. -/
theorem abs_sum_log_one_sub_add_le {ι : Type*} (s : Finset ι) (h : ι → ℝ)
    {δ : ℝ} (hδ : δ ≤ 1 / 2) (hh : ∀ i ∈ s, 0 ≤ h i ∧ h i ≤ δ) :
    |(∑ i ∈ s, Real.log (1 - h i)) + ∑ i ∈ s, h i| ≤
      2 * δ * ∑ i ∈ s, h i := by
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ s, |Real.log (1 - h i) + h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, 2 * δ * h i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hh i hi
      exact (abs_log_one_sub_add_le h.1 (h.2.trans hδ)).trans (by nlinarith)
    _ = _ := by rw [Finset.mul_sum]

/-- A triangular finite survival product converges to the exponential of the
negative total rate when all its individual hazards vanish uniformly. -/
theorem tendsto_finite_survival_product {ι : Type*} {s : ℕ → Finset ι}
    {h : ℕ → ι → ℝ} {δ : ℕ → ℝ} {L : ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hh : ∀ᶠ n in atTop, ∀ i ∈ s n, 0 ≤ h n i ∧ h n i ≤ δ n)
    (hsum : Tendsto (fun n ↦ ∑ i ∈ s n, h n i) atTop (𝓝 L)) :
    Tendsto (fun n ↦ ∏ i ∈ s n, (1 - h n i)) atTop (𝓝 (Real.exp (-L))) := by
  have hsmall : ∀ᶠ n in atTop, δ n ≤ 1 / 2 :=
    (hδ.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono fun _ h ↦ h.le
  have hbound : Tendsto (fun n ↦ 2 * δ n * ∑ i ∈ s n, h n i) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hδ).mul hsum
  have herr : Tendsto (fun n ↦ (∑ i ∈ s n, Real.log (1 - h n i)) +
      ∑ i ∈ s n, h n i) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hbound
    filter_upwards [hsmall, hh] with n hn hh
    simpa only [Real.norm_eq_abs] using abs_sum_log_one_sub_add_le (s n) (h n) hn hh
  have hlogs : Tendsto (fun n ↦ ∑ i ∈ s n, Real.log (1 - h n i)) atTop (𝓝 (-L)) := by
    simpa using herr.sub hsum
  apply (Real.continuous_exp.tendsto (-L) |>.comp hlogs).congr'
  filter_upwards [hsmall, hh] with n hn hh
  simp only [Function.comp_def]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.exp_log (by have := hh i hi; linarith)

end Freezing2
