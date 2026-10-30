module

public import Freezing2.Analysis.ProfilePrimitive
public import Freezing2.Discrete.HarmonicDistances
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniformly small normalized harmonic sums on short intervals

Global reciprocal-profile convergence controls intervals near both endpoints.
This is the deterministic link between sublinear coalescence delay and the
segment-distance approximation in the subcritical main result.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The inclusive sum differs from a difference of normalized prefixes by its
single left endpoint. -/
theorem normalized_inclusiveHarmonic_eq (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (n : ℝ) ^ (α - 1) * inclusiveHarmonic (x n) a b =
      (n : ℝ) ^ (α - 1) * (activeCount (x n) a : ℝ)⁻¹ +
        2 * (normalizedHarmonicPrefix x α n b - normalizedHarmonicPrefix x α n a) := by
  rw [inclusiveHarmonic_eq _ hab, ← harmonicInterval_prefix_difference _ hab]
  unfold normalizedHarmonicPrefix
  ring

/-- One positive length threshold works for every short interval and every
sufficiently large horizon, including intervals touching zero or one. -/
theorem eventually_uniform_short_harmonic_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1) (hL1 : HasL1ReciprocalProfile x α g)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ,
      a ≤ b → b ≤ n → (b : ℝ) - a ≤ δ * n →
        (n : ℝ) ^ (α - 1) * inclusiveHarmonic (x n) a b < η := by
  have huc : UniformContinuousOn (profilePrimitive g) (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (continuous_profilePrimitive hL1.1).continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc
    (η / 8) (by positivity)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hC : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    have he := tendsto_profile_spike_bound hα (by norm_num : (0 : ℝ) < 2)
    apply he.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]
    simp
  filter_upwards [(tendsto_branchPrimitiveError hα hL1).eventually_lt_const
      (show 0 < η / 16 by positivity),
    hC.eventually_lt_const (show 0 < η / 4 by positivity), eventually_gt_atTop 0]
    with n he hCn hn
  intro a b hab hbn hlen
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have han := hab.trans hbn
  have ha01 : (a : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hn').mpr (by exact_mod_cast han)⟩
  have hb01 : (b : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hn').mpr (by exact_mod_cast hbn)⟩
  have hba : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hdist : dist ((b : ℝ) / n) ((a : ℝ) / n) < δ := by
    rw [Real.dist_eq, ← sub_div, abs_of_nonneg (div_nonneg (by linarith) hn'.le)]
    apply (div_lt_iff₀ hn').mpr
    nlinarith
  have hm := hmod _ hb01 _ ha01 hdist
  rw [Real.dist_eq] at hm
  have hea := normalizedHarmonicPrefix_error_le (α := α) hx hL1.1 hn han
  have heb := normalizedHarmonicPrefix_error_le (α := α) hx hL1.1 hn hbn
  have hS : (1 : ℝ) ≤ activeCount (x n) a := by
    have hs := (hx n).2 a han
    have hs' : (1 : ℤ) ≤ activeCount (x n) a := by omega
    exact_mod_cast hs'
  have hinv : (activeCount (x n) a : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith)).mpr hS
  have hCnonneg : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg hn'.le _
  have hendpoint := mul_le_mul_of_nonneg_left hinv hCnonneg
  rw [mul_one] at hendpoint
  rw [normalized_inclusiveHarmonic_eq x α n hab]
  have ha := (abs_le.mp hea).1
  have hb := (abs_le.mp heb).2
  have hm' := (abs_lt.mp hm).2
  linarith

end Freezing2
