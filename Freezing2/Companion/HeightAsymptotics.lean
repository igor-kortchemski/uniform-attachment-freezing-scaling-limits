module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.HeightTailBounds

/-!
# Negligible logarithmic union factors

These estimates retain the actual `n+1` vertex bound and the one-edge shift
arising from the direct forward construction. They are deterministic inputs
to the maximum-height limits, not hypotheses substituted for tree estimates.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

theorem log_nat_succ_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  calc
    Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) * n) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = 2 * Real.log (n : ℝ) := by rw [Real.log_mul hp.ne' hp.ne']; ring

theorem eventually_log_nat_succ_le_mul_scale {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ a * h n := by
  filter_upwards [eventually_ge_atTop 2, hdiv.eventually_gt_atTop 0,
    hlog.eventually (gt_mem_nhds (half_pos ha))] with n hn hhn hsmall
  have hs := (div_lt_iff₀ hhn).mp hsmall
  have hb := log_nat_succ_le_two_log hn
  nlinarith

theorem eventually_nat_succ_le_exp_scale {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 ≤ Real.exp (h n) := by
  filter_upwards [eventually_log_nat_succ_le_mul_scale hdiv hlog zero_lt_one] with n hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  simpa only [Real.exp_log hpos, one_mul] using Real.exp_le_exp.mpr hn

/-- Any positive exponential rate beats the finite union factor when
`log n = o(h_n)`. -/
theorem tendsto_nat_succ_mul_exp_neg_of_log_negligible {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-h n * a)) atTop (𝓝 0) := by
  have he : Tendsto (fun n => Real.exp (-h n * (a / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := tendsto_neg_atTop_atBot.comp (hdiv.atTop_mul_const (half_pos ha))
    change Tendsto (fun n : ℕ => -(h n * (a / 2))) atTop atBot at hh
    simpa only [neg_mul] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ he
  filter_upwards [eventually_log_nat_succ_le_mul_scale hdiv hlog (half_pos ha)] with n hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  calc
    ((n : ℝ) + 1) * Real.exp (-h n * a) =
        Real.exp (Real.log ((n : ℝ) + 1) - h n * a) := by
      rw [neg_mul, Real.exp_neg, Real.exp_sub, Real.exp_log hpos, div_eq_mul_inv]
    _ ≤ Real.exp (-h n * (a / 2)) := Real.exp_le_exp.mpr (by nlinarith)

theorem tendsto_shifted_bennett_upper_of_log_negligible {h : ℕ → ℝ}
    (hdiv : Tendsto h atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / h n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Real.exp (-h n * bennettRate (ε - 1 / h n))) atTop (𝓝 0) := by
  have hb := tendsto_nat_succ_mul_exp_neg_of_log_negligible hdiv hlog
    (bennettRate_pos (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hb
  filter_upwards [hdiv.eventually_gt_atTop 0, hdiv.eventually_ge_atTop (2 / ε)] with n hn hne
  have hs : 1 / h n ≤ ε / 2 := by
    apply (div_le_iff₀ hn).mpr
    have hm := (div_le_iff₀ hε).mp hne
    nlinarith
  have hle : ε / 2 ≤ ε - 1 / h n := by linarith
  have hg := strictMonoOn_bennettRate.monotoneOn (by positivity : 0 ≤ ε / 2)
    (by linarith : 0 ≤ ε - 1 / h n) hle
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

end Freezing1
