module

public import Freezing2.Analysis.ProfileIntegrals
public import Freezing2.Analysis.LocalL1

/-!
# Sublinear populations from reciprocal-profile convergence

This proves Lemma `lem:hnalpha(i)` using only its global L¹ hypothesis.
A macroscopic population at a fixed positive time forces the reciprocal profile
to vanish on a fixed preceding interval, contradicting the positive limiting
integral there. The rounding loss is explicit in `reciprocalProfile_le_of_spike`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- Every fixed positive-time population is sublinear. The local L² condition
and the lower bound `0 < α` in the paper are unnecessary for this conclusion. -/
theorem population_sublinear_at {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min a ε / 4
  let J : Set ℝ := Icc (a - δ) a
  have hδ0 : 0 < δ := div_pos (lt_min ha0 hε) (by norm_num)
  have hδa : δ ≤ a := by dsimp [δ]; have := min_le_left a ε; linarith
  have hδε : δ ≤ ε / 4 := div_le_div_of_nonneg_right (min_le_right a ε) (by norm_num)
  have hJ : J ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨by have := ht.1; linarith, ht.2.trans ha1⟩
  have hμJ : profileMeasure J ≠ 0 := by
    rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hJ]
    rw [Real.volume_Icc]
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    linarith
  have hc : 0 < ∫ t in J, g t ∂profileMeasure :=
    setIntegral_pos_of_ae_pos hL1.1 hpos hμJ
  have hA := tendsto_setIntegral_of_l1
    (fun n ↦ integrable_reciprocalProfile x α n) hL1.1 hL1.2 J
  have hB : Tendsto (fun n : ℕ ↦ profileMeasure.real J *
      ((2 / ε) * ((n : ℝ) ^ α / n))) atTop (𝓝 0) := by
    simpa using (tendsto_profile_spike_bound hα hε).const_mul (profileMeasure.real J)
  have hnlarge : ∀ᶠ n : ℕ in atTop, 4 ≤ ε * (n : ℝ) := by
    have hn : ∀ᶠ n : ℕ in atTop, 4 / ε ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4 / ε))
    filter_upwards [hn] with n hn
    have := (div_le_iff₀ hε).mp hn
    simpa only [mul_comm] using this
  have hevent : ∀ᶠ n : ℕ in atTop,
      ¬ ε * (n : ℝ) ≤ activeCount (x n) ⌊(n : ℝ) * a⌋₊ := by
    apply eventually_not_of_tendsto_pos_of_bound hA hc hB
    filter_upwards [hnlarge] with n hn hspike
    calc
      _ ≤ ∫ _ in J, (2 / ε) * ((n : ℝ) ^ α / n) ∂profileMeasure := by
        apply setIntegral_mono_on (integrable_reciprocalProfile x α n).restrict
          (integrable_const _) measurableSet_Icc
        intro t ht
        exact reciprocalProfile_le_of_spike x α n (hx n).1 hε hn
          (hJ ht).1 ht.2 ht.1 hδε hspike
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  filter_upwards [hevent, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hfloor : ⌊(n : ℝ) * a⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    simpa using mul_le_mul_of_nonneg_left ha1 hnpos.le
  have hcount : (0 : ℝ) ≤ activeCount (x n) ⌊(n : ℝ) * a⌋₊ := by
    exact_mod_cast ((hx n).2 _ hfloor).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hcount hnpos.le)]
  apply (div_lt_iff₀ hnpos).mpr
  simpa only [mul_comm] using lt_of_not_ge hn

end Freezing2
