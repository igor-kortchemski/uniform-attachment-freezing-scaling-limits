module

public import Freezing2.Analysis.SupercriticalCoalescence

/-!
# The compact-interval hazard rate in the supercritical proof

This records the explicit `O(n^(1-2*α))` estimate in U21. The single constant
works simultaneously for every integer interval inside the fixed cutoff.
The estimate itself holds throughout `0 < α < 1`; it tends to zero when
`α > 1/2`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

/-- The error bound in N06(v) supplies a fixed compact-interval rate constant,
uniform over both interval endpoints. -/
theorem eventually_uniform_coalescence_hazard_rate
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ,
      CoalescenceInterval ε n a b →
        2 * coalescenceUpSum (x n) (a - 1) (b + 1 - a) ≤
          C * (n : ℝ) ^ (1 - 2 * α) := by
  let δ : ℝ := min ε (1 / 4)
  let K : ℝ := ∫ t in Icc δ (1 - δ), (g t) ^ 2
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδgap : δ < 1 - δ := by
    have hd : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  have hg2 := (h2 δ (1 - δ) hδ hδgap (by linarith)).1
  have hK : 0 ≤ K := integral_nonneg (fun _ ↦ sq_nonneg _)
  refine ⟨2 + K, by linarith, ?_⟩
  filter_upwards [eventually_coalescenceIntervalError_lt hx hα0 hα1 hL1 hpos h2 hε
    (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop 0] with n he hn
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
  let Q : ℝ := (n : ℝ) ^ (2 * α) / n
  have hQ : 0 < Q := div_pos (Real.rpow_pos_of_pos hn' _) hn'
  change |Q * coalescenceUpSum (x n) (a - 1) (b + 1 - a) -
    (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), (g t) ^ 2) / 2| < 1 at herr
  have hupper := (abs_lt.mp herr).2
  have hbound : 2 * coalescenceUpSum (x n) (a - 1) (b + 1 - a) ≤ (2 + K) / Q := by
    apply (le_div_iff₀ hQ).mpr
    nlinarith
  have hpow : (n : ℝ) ^ (1 - 2 * α) = Q⁻¹ := by
    rw [show 1 - 2 * α = -(2 * α - 1) by ring, Real.rpow_neg hn'.le,
      Real.rpow_sub hn', Real.rpow_one]
  simpa only [hpow, div_eq_mul_inv] using hbound

/-- Nonnegativity justifies the ordinary absolute-value meaning of the
manuscript's big-O assertion. -/
theorem coalescence_hazard_nonneg_of_interval {x : ℕ → ℤ} {ε : ℝ} {n a b : ℕ}
    (hs : SurvivesThrough x n) (hab : CoalescenceInterval ε n a b) :
    0 ≤ 2 * coalescenceUpSum x (a - 1) (b + 1 - a) := by
  apply mul_nonneg (by norm_num)
  unfold coalescenceUpSum
  apply Finset.sum_nonneg
  intro i hi
  apply coalescenceUpSum_term_nonneg x hs
  have := Finset.mem_range.mp hi
  rcases hab with ⟨ha, hab, hbn, _, _⟩
  omega

/-- U21's printed hazard order, for any varying endpoints in a fixed compact
interior interval. The uniform theorem above gives the same constant for all
such choices. -/
theorem isBigO_coalescence_hazard_of_eventually_interval
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε)
    {a b : ℕ → ℕ} (hab : ∀ᶠ n in atTop, CoalescenceInterval ε n (a n) (b n)) :
    (fun n ↦ 2 * coalescenceUpSum (x n) (a n - 1) (b n + 1 - a n))
      =O[atTop] (fun n ↦ (n : ℝ) ^ (1 - 2 * α)) := by
  obtain ⟨C, _, hC⟩ := eventually_uniform_coalescence_hazard_rate hx hα0 hα1 hL1 hpos h2 hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC, hab] with n hn hnab
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (coalescence_hazard_nonneg_of_interval (hx n).2 hnab),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn (a n) (b n) hnab

end Freezing2
