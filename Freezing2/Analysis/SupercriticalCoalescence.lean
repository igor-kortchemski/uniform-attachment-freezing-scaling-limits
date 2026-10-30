module

public import Freezing2.Analysis.SubcriticalCoalescence

/-!
# Vanishing coalescence hazard on compact interior intervals

In the supercritical regime, the unscaled coalescence sum tends to zero
uniformly over every integer interval inside a fixed compact subinterval of
`(0,1)`. This is the deterministic input to the sampled-pair estimate N10.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The local square-profile convergence bounds the unscaled hazard uniformly
over all interior windows when `α > 1/2`. -/
theorem eventually_uniform_supercritical_coalescence_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ, CoalescenceInterval ε n a b →
      2 * coalescenceUpSum (x n) (a - 1) (b + 1 - a) < η := by
  let δ : ℝ := min ε (1 / 4)
  let K : ℝ := ∫ t in Icc δ (1 - δ), (g t) ^ 2
  let C : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (2 * α) / n
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδgap : δ < 1 - δ := by
    have hd : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hδ1 : 1 - δ < 1 := by linarith
  have hg2 := (h2 δ (1 - δ) hδ hδgap hδ1).1
  have hC : Tendsto C atTop atTop := by
    apply ((tendsto_rpow_atTop (show 0 < 2 * α - 1 by linarith)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp [C]
    rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]
  have hlim : Tendsto (fun n ↦ (2 + K) / C n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hC
  filter_upwards [eventually_coalescenceIntervalError_lt hx (by linarith) hα1
      hL1 hpos h2 hε (by norm_num : (0 : ℝ) < 1),
    hlim.eventually_lt_const hη, eventually_gt_atTop 0] with n he hnη hn
  intro a b hvalid
  have herr := he a b hvalid
  rcases hvalid with ⟨ha, hab, hbn, hlo, hhi⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : Icc ((a : ℝ) / n) ((b : ℝ) / n) ⊆ Icc δ (1 - δ) := by
    intro t ht
    constructor
    · have hδn := mul_le_mul_of_nonneg_right hδε hn'.le
      exact ((le_div_iff₀ hn').mpr (hδn.trans hlo)).trans ht.1
    · have hδn := mul_le_mul_of_nonneg_right (show 1 - ε ≤ 1 - δ by linarith) hn'.le
      exact ht.2.trans ((div_le_iff₀ hn').mpr (hhi.trans hδn))
  have hI : (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), (g t) ^ 2) ≤ K :=
    setIntegral_mono_set hg2 (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall fun _ ht ↦ hsub ht)
  have hCp : 0 < C n := div_pos (Real.rpow_pos_of_pos hn' _) hn'
  change |C n * coalescenceUpSum (x n) (a - 1) (b + 1 - a) -
    (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), (g t) ^ 2) / 2| < 1 at herr
  have hupper := (abs_lt.mp herr).2
  have hbound : 2 * coalescenceUpSum (x n) (a - 1) (b + 1 - a) ≤
      (2 + K) / C n := by
    apply (le_div_iff₀ hCp).mpr
    nlinarith
  exact hbound.trans_lt hnη

end Freezing2
