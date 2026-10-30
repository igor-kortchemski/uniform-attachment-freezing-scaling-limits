module

public import Freezing2.Analysis.CriticalIsolationRate
public import Mathlib.Analysis.Real.Sqrt

/-!
# Comparison with the source logarithmic covering radius

The factor-sixteen occupancy blocks and all ceiling/floor errors fit inside
the source radius n log(k)^2 / sqrt(k), uniformly for n≥k, once k is large
depending only on the population bound M.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

theorem criticalBlockRadius_le_log_squared {M : ℝ} (hM : 0 ≤ M)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hlog : 3200 * (M + 1) ≤ Real.log k) :
    2 * (criticalIsolationWindow k : ℝ) *
      ((16 * ⌈M * n / Real.sqrt k⌉₊ : ℕ) : ℝ) ≤
        Real.log k ^ 2 / Real.sqrt k * n := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hsN : Real.sqrt (k : ℝ) ≤ n :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hkR)).trans hknR
  have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkR
  have hp : (criticalIsolationWindow k : ℝ) ≤ 100 * Real.log k :=
    Nat.floor_le (by positivity)
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ M * n / Real.sqrt k by positivity)).le
  have hcMul : (⌈M * n / Real.sqrt k⌉₊ : ℝ) * Real.sqrt k ≤ M * n + Real.sqrt k := by
    have h := mul_le_mul_of_nonneg_right hc hs.le
    simpa only [add_mul, div_mul_cancel₀ _ hs.ne', one_mul] using h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hs).mpr
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = 32 * (criticalIsolationWindow k : ℝ) *
        ((⌈M * n / Real.sqrt k⌉₊ : ℝ) * Real.sqrt k) := by ring
    _ ≤ 32 * (100 * Real.log k) * (M * n + Real.sqrt k) := by gcongr
    _ ≤ 32 * (100 * Real.log k) * (M * n + n) := by gcongr
    _ = 3200 * (M + 1) * (Real.log k * n) := by ring
    _ ≤ Real.log k * (Real.log k * n) :=
      mul_le_mul_of_nonneg_right hlog (mul_nonneg hlog0 hn0)
    _ = _ := by ring

/-- The cutoff depends only on M, before the horizon n is quantified. -/
theorem eventually_uniform_criticalBlockRadius {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℕ, ∀ k ≥ K, 2 ≤ criticalIsolationWindow k ∧
      ∀ n ≥ k, 2 * (criticalIsolationWindow k : ℝ) *
        ((16 * ⌈M * n / Real.sqrt k⌉₊ : ℕ) : ℝ) ≤
          Real.log k ^ 2 / Real.sqrt k * n := by
  have hlim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop (3200 * (M + 1))))
  refine ⟨max 1 K, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hlog : 3200 * (M + 1) ≤ Real.log k := hK k ((le_max_right _ _).trans hk)
  refine ⟨?_, fun n hn ↦ criticalBlockRadius_le_log_squared hM hk1 hn hlog⟩
  unfold criticalIsolationWindow
  apply Nat.le_floor
  norm_num only [Nat.cast_ofNat]
  nlinarith

end Freezing2
