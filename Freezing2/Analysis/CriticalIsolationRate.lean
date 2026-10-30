module

public import Freezing2.Analysis.ExponentialDecay
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Decay of the alternating-block isolation bound

The logarithmic window is the manuscript's `floor(100 log k)`. The number
of usable alternating blocks is rounded down, with both rounding losses
retained. The resulting geometric error is uniformly negligible at order k⁻⁴.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

noncomputable def criticalIsolationWindow (k : ℕ) : ℕ := ⌊100 * Real.log k⌋₊

noncomputable def criticalIsolationTrials (k : ℕ) : ℕ :=
  (criticalIsolationWindow k - 1) / 2

theorem criticalIsolationTrials_lower_bound (k : ℕ) :
    50 * Real.log k - 2 ≤ (criticalIsolationTrials k : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (100 * Real.log (k : ℝ))
  have hdiv : criticalIsolationWindow k ≤ 2 * criticalIsolationTrials k + 2 := by
    unfold criticalIsolationTrials
    omega
  have hr : (criticalIsolationWindow k : ℝ) ≤ 2 * (criticalIsolationTrials k : ℝ) + 2 := by
    exact_mod_cast hdiv
  change 100 * Real.log (k : ℝ) < (criticalIsolationWindow k : ℝ) + 1 at hfloor
  linarith

theorem criticalIsolation_geometric_bound {k : ℕ} (hk : 0 < k) :
    (3 / 4 : ℝ) ^ criticalIsolationTrials k ≤
      Real.exp (-2 * Real.log (3 / 4)) * (k : ℝ) ^ (50 * Real.log (3 / 4)) := by
  have hq : (0 : ℝ) < 3 / 4 := by norm_num
  have h := Real.rpow_le_rpow_of_exponent_ge hq (by norm_num : (3 / 4 : ℝ) ≤ 1)
    (criticalIsolationTrials_lower_bound k)
  rw [Real.rpow_natCast] at h
  refine h.trans_eq ?_
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos (by exact_mod_cast hk : (0 : ℝ) < k),
    ← Real.exp_add]
  congr 1
  ring

theorem tendsto_scaled_criticalIsolationProbability :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ 4 * (3 / 4 : ℝ) ^ criticalIsolationTrials k)
      atTop (𝓝 0) := by
  have hexp : 4 + 50 * Real.log (3 / 4) < 0 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    linarith
  have hlim := (tendsto_rpow_neg_atTop (neg_pos.mpr hexp)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [neg_neg, Function.comp_def] at hlim
  have hlim' := hlim.const_mul (Real.exp (-2 * Real.log (3 / 4)))
  simp only [mul_zero] at hlim'
  apply squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hlim'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h := mul_le_mul_of_nonneg_left (criticalIsolation_geometric_bound (by omega : 0 < k))
    (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 4)
  convert h using 1
  rw [Real.rpow_add hk0]
  norm_num only [Real.rpow_ofNat]
  ring

end Freezing2
