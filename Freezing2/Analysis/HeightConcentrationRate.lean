module

public import Freezing2.Analysis.BennettFunction
public import Freezing2.Analysis.ExponentialDecay
public import Freezing2.Analysis.HeightNormalization

/-!
# The positive exponential rate in uniform height concentration

A mean scale asymptotic to a positive multiple of `n^β` gives a Bennett
exponent at least a positive multiple of `n^β`. Consequently the quadratic
union factor tends to zero. The source's harmonic scale supplies these
assumptions; no stochastic height representation is asserted here.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- The positive constant in the exponential rate is derived from the limiting
mean scale and the requested deviation, rather than assumed. -/
theorem eventually_bennettExponent_ge_rpow {H : ℕ → ℝ} {β L ε : ℝ}
    (hscale : Tendsto (fun n : ℕ ↦ H n / (n : ℝ) ^ β) atTop (𝓝 L))
    (hL : 0 < L) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ β ≤ bennettExponent (ε * (n : ℝ) ^ β) (H n) := by
  let c : ℝ := 2 * L * bennettFunction (ε / (2 * L))
  have hc : 0 < c := mul_pos (by positivity) (bennettFunction_pos (by positivity))
  refine ⟨c, hc, ?_⟩
  filter_upwards [hscale.eventually_const_lt hL,
    hscale.eventually_lt_const (show L < 2 * L by linarith), eventually_gt_atTop 0]
    with n hnlow hnupper hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' _
  have hH : 0 < H n := by
    simpa only [zero_mul] using (lt_div_iff₀ hs).mp hnlow
  have hupper : H n ≤ 2 * L * (n : ℝ) ^ β := (div_lt_iff₀ hs).mp hnupper |>.le
  have hcomp := bennettExponent_le_of_le (mul_pos hε hs) hH hupper
  have he : bennettExponent (ε * (n : ℝ) ^ β) (2 * L * (n : ℝ) ^ β) =
      c * (n : ℝ) ^ β := by
    have hratio : ε * (n : ℝ) ^ β / (2 * L * (n : ℝ) ^ β) = ε / (2 * L) := by
      field_simp
    rw [bennettExponent, hratio]
    dsimp [c]
    ring
  rwa [he] at hcomp

/-- The quadratic finite-family Bennett bound vanishes at every positive
polynomial height scale. -/
theorem tendsto_quadratic_bennett_bound {H : ℕ → ℝ} {β L ε : ℝ}
    (hβ : 0 < β) (hscale : Tendsto (fun n : ℕ ↦ H n / (n : ℝ) ^ β) atTop (𝓝 L))
    (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) + 1) ^ 2 *
      Real.exp (-bennettExponent (ε * (n : ℝ) ^ β) (H n))) atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := eventually_bennettExponent_ge_rpow hscale hL hε
  have hlim := (tendsto_nat_succ_sq_mul_exp_neg_rpow hβ hc).const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    (by simpa only [mul_zero, mul_assoc] using hlim)
  filter_upwards [hbound] with n hn
  simpa only [mul_assoc, neg_mul] using
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hn))
      (show 0 ≤ 2 * ((n : ℝ) + 1) ^ 2 by positivity)

/-- Source lines 910–915: the actual harmonic scale gives a vanishing uniform
Bennett bound at deviations `ε n^(1−α)`. -/
theorem tendsto_uniform_height_bennett_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) + 1) ^ 2 *
      Real.exp (-bennettExponent (ε * (n : ℝ) ^ (1 - α)) (harmonicUpTotal x n)))
      atTop (𝓝 0) :=
  tendsto_quadratic_bennett_bound (sub_pos.mpr hα1)
    (tendsto_harmonicUpTotal_div_rpow hx hα0 hα1 hL1 hpos)
    (harmonicUp_limit_pos hL1 hpos) hε

end Freezing2
