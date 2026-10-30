module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.ForwardMaximum
public import Freezing2.Companion.HeightAsymptotics
public import Freezing2.Companion.MaximumMGFLimits

/-!
# The main maximum-height theorems

These are parts II and III of Theorem `thm:height`, for the actual forward
tree distribution. The proof uses the direct forward MGF bounds, retaining
their finite `n+1` prefactor and one-edge shift until the asymptotic passage.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped Topology ENNReal

theorem normalized_treeHeight_lower_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {ε : ℝ} (hε : 0 < ε) :
    (Forward.treeLaw x n).real {s | (Forward.treeHeight s : ℝ) / heightScale x n < 1 - ε} ≤
      Real.exp (-heightScale x n * bennettRate ε) := by
  have hm := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hbound := Forward.treeHeight_lower_tail x n hn hτ (mul_pos hε hm)
  have hq : ε * heightScale x n / heightScale x n = ε := by field_simp
  rw [hq] at hbound
  convert hbound using 1
  congr 1
  ext s
  change (Forward.treeHeight s : ℝ) / heightScale x n < 1 - ε ↔
    (Forward.treeHeight s : ℝ) < heightScale x n - ε * heightScale x n
  rw [div_lt_iff₀ hm]
  ring_nf

theorem normalized_treeHeight_upper_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {ε : ℝ} (ht : 0 < ε * heightScale x n - 1) :
    (Forward.treeLaw x n).real {s | 1 + ε < (Forward.treeHeight s : ℝ) / heightScale x n} ≤
      (n + 1) * Real.exp (-heightScale x n * bennettRate (ε - 1 / heightScale x n)) := by
  have hm := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hbound := Forward.treeHeight_upper_tail x n hn hτ ht
  have hq : (ε * heightScale x n - 1) / heightScale x n = ε - 1 / heightScale x n := by field_simp
  rw [hq] at hbound
  convert hbound using 1
  congr 1
  ext s
  change 1 + ε < (Forward.treeHeight s : ℝ) / heightScale x n ↔
    heightScale x n + 1 + (ε * heightScale x n - 1) < (Forward.treeHeight s : ℝ)
  rw [lt_div_iff₀ hm]
  ring_nf

theorem maximum_height_lower_probability_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | (Forward.treeHeight s : ℝ) / heightScale (x n) n < 1 - ε}) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  have he : Tendsto (fun n => Real.exp (-heightScale (x n) n * bennettRate ε)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := tendsto_neg_atTop_atBot.comp (hd.atTop_mul_const (bennettRate_pos hε))
    change Tendsto (fun n : ℕ => -(heightScale (x n) n * bennettRate ε)) atTop atBot at hh
    simpa only [neg_mul] using hh
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ he
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact normalized_treeHeight_lower_tail (x n) n hn (hτ n) hε

theorem maximum_height_upper_probability_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | 1 + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n}) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (tendsto_shifted_bennett_upper_of_log_negligible hd hlog hε)
  filter_upwards [eventually_ge_atTop 1, hd.eventually_gt_atTop (1 / ε)] with n hn hlarge
  have ht : 0 < ε * heightScale (x n) n - 1 := by
    have hh := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  exact normalized_treeHeight_upper_tail (x n) n hn (hτ n) ht

theorem maximum_height_universal_upper_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | Real.exp 1 + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n}) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  have hlower : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) / 4) ≤ heightScale (x n) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact log_quarter_le_heightScale hn ((lt_extinctionTime_iff (x n) n).mp (hτ n))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (tendsto_shifted_bennett_upper_bound hlower hε)
  have he : 0 < Real.exp 1 - 1 + ε := by
    have := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  filter_upwards [eventually_ge_atTop 1, hd.eventually_gt_atTop (1 / (Real.exp 1 - 1 + ε))]
    with n hn hlarge
  have ht : 0 < (Real.exp 1 - 1 + ε) * heightScale (x n) n - 1 := by
    have hh := (div_lt_iff₀ he).mp hlarge
    nlinarith
  have hb := normalized_treeHeight_upper_tail (x n) n hn (hτ n) ht
  simpa only [show 1 + (Real.exp 1 - 1 + ε) = Real.exp 1 + ε by ring] using hb

/-- Theorem `thm:height` (II): the universal maximum-height window. -/
theorem maximum_height_window_tendsto_one (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {ε : ℝ}
    (hε : 0 < ε) (_hε1 : ε < 1) :
    Tendsto (fun n => (Forward.treeLaw (x n) n).real
      {s | 1 - ε ≤ (Forward.treeHeight s : ℝ) / heightScale (x n) n ∧
        (Forward.treeHeight s : ℝ) / heightScale (x n) n ≤ Real.exp 1 + ε}) atTop (𝓝 1) := by
  let bad (n : ℕ) : Set Forward.State :=
    {s | (Forward.treeHeight s : ℝ) / heightScale (x n) n < 1 - ε} ∪
      {s | Real.exp 1 + ε < (Forward.treeHeight s : ℝ) / heightScale (x n) n}
  have hb : Tendsto (fun n => (Forward.treeLaw (x n) n).real (bad n)) atTop (𝓝 0) := by
    have hl := (maximum_height_lower_probability_tendsto_zero x hτ hε).add
      (maximum_height_universal_upper_tendsto_zero x hτ hε)
    simp only [add_zero] at hl
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun _ => measureReal_union_le _ _) hl
  have hh := (tendsto_const_nhds (x := (1 : ℝ)) :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hb
  simp only [sub_zero] at hh
  convert hh using 1
  funext n
  rw [← probReal_compl_eq_one_sub (by trivial : MeasurableSet (bad n))]
  congr 1
  ext s
  simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt]

/-- Convergence in probability of the normalized maximum under `log n = o(h_n⁺)`. -/
theorem maximum_height_deviation_tendsto_zero (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Forward.treeLaw (x n) n)
      {s | ε ≤ |(Forward.treeHeight s : ℝ) / heightScale (x n) n - 1|}) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
  have hl := (maximum_height_lower_probability_tendsto_zero x hτ (half_pos hε)).add
    (maximum_height_upper_probability_tendsto_zero x hτ hlog (half_pos hε))
  simp only [add_zero] at hl
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hl
  intro n
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro s hs
  change ε ≤ |(Forward.treeHeight s : ℝ) / heightScale (x n) n - 1| at hs
  change (Forward.treeHeight s : ℝ) / heightScale (x n) n < 1 - ε / 2 ∨
    1 + ε / 2 < (Forward.treeHeight s : ℝ) / heightScale (x n) n
  rcases le_abs.mp hs with h | h
  · right; linarith
  · left; linarith

/-- Theorem `thm:height` (III): all real `Lp` maximum-height convergence. -/
theorem maximum_height_tendsto_Lp (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (x n) n) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun s => (Forward.treeHeight s : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.treeLaw (x n) n)) atTop (𝓝 0) := by
  have hd := tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  apply normalized_tendsto_Lp_of_eventual_exp_bound
    (Z := fun _ s => (Forward.treeHeight s : ℝ)) (a := fun n => heightScale (x n) n)
    (B := Real.exp 1 + 1)
  · intro n; exact measurable_from_top
  · intro n θ; exact Forward.treeLaw_integrable_exp_treeHeight (x n) n θ
  · intro n; exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [eventually_nat_succ_le_exp_scale hd hlog, hd.eventually_ge_atTop 1]
      with n hn hm
    exact Forward.treeHeight_mgf_one_le (x n) n (hτ n) hn hm
  · exact hd
  · intro ε hε; exact maximum_height_deviation_tendsto_zero x hτ hlog hε
  · exact hp

end Freezing1
