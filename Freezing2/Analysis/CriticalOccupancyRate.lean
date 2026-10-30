module

public import Freezing2.Analysis.BennettFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Uniform critical occupancy error rate

The repaired frozen-block proof has an exponentially small occupancy error
and a fourfold-collision error of order k⁻⁵ when k³≤n. Their sum is o(k⁻⁴),
with constants independent of the larger horizon n.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Freezing2

noncomputable def criticalOccupancyError (M : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt k / (16 * M) * Real.exp (-6 * M * Real.sqrt k * bennettFunction (1 / 4)) +
    8 / (k : ℝ) ^ 5

theorem criticalOccupancyError_nonneg {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    0 ≤ criticalOccupancyError M k := by
  unfold criticalOccupancyError
  positivity

/-- The bound is small relative to k⁻⁴, with the constant M fixed before k. -/
theorem tendsto_scaled_criticalOccupancyError {M : ℝ} (hM : 0 < M) :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ 4 * criticalOccupancyError M k) atTop (𝓝 0) := by
  have hc : 0 < 6 * M * bennettFunction (1 / 4) :=
    mul_pos (by positivity) (bennettFunction_pos (by norm_num))
  have hs : Tendsto (fun k : ℕ ↦ Real.sqrt (k : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    9 (6 * M * bennettFunction (1 / 4)) hc).comp hs
  have hd := he.div_const (16 * M)
  have hi := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 8
  have h := hd.add hi
  simp only [zero_div, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  simp only [Function.comp_apply]
  rw [show (9 : ℝ) = (9 : ℕ) by norm_num, Real.rpow_natCast]
  unfold criticalOccupancyError
  rw [show -(6 * M * bennettFunction (1 / 4)) * Real.sqrt k =
    -6 * M * Real.sqrt k * bennettFunction (1 / 4) by ring]
  have hp : Real.sqrt (k : ℝ) ^ 9 = (k : ℝ) ^ 4 * Real.sqrt k := by
    calc
      _ = (Real.sqrt (k : ℝ) ^ 2) ^ 4 * Real.sqrt k := by ring
      _ = _ := by rw [hsquare]
  rw [hp]
  field_simp

end Freezing2
