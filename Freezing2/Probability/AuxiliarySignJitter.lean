module

public import Freezing2.Probability.MeshJitter

/-!
# Lebesgue-dominated auxiliary sign-time laws

Jittering a source sign index inside its mesh cell leaves its weak limit
unchanged and gives an eventually uniform density bound. This is the bridge
from local L1 profile convergence to rates sampled at attachment times.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal NNReal

namespace Freezing2

theorem auxiliarySignTimes_card (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) :
    (auxiliarySignTimes x σ n).card = (auxiliarySignSteps x σ n).card := by
  rw [← auxiliarySignSteps_image_pred,
    Finset.card_image_of_injOn (auxiliarySignSteps_pred_injOn x σ n)]

theorem eventually_auxiliarySignTimes_nonempty_of_signMeasure {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    ∀ᶠ n in atTop, (auxiliarySignTimes (x n) σ n).Nonempty := by
  filter_upwards [eventually_auxiliarySignSteps_nonempty_of_signMeasure h] with n hn
  rw [← Finset.card_ne_zero, auxiliarySignTimes_card]
  exact hn.card_pos.ne'

theorem tendsto_auxiliarySignTimes_card_div {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    Tendsto (fun n : ℕ ↦ ((auxiliarySignTimes (x n) σ n).card : ℝ) / n)
      atTop (𝓝 (1 / 2)) := by
  have hm : Tendsto (fun n ↦ ((signTimeMeasure (x n) σ n).mass : ℝ)) atTop (𝓝 1) := by
    simpa only [profileFiniteMeasure_mass] using NNReal.tendsto_coe.mpr h.mass
  convert hm.div_const 2 using 1
  funext n
  rw [auxiliarySignTimes_card]
  change _ = ((meshCountingMeasure n (auxiliarySignSteps (x n) σ n)).mass : ℝ) / 2
  rw [meshCountingMeasure_mass]
  ring

/-- The jittered version of the source's zero-based sign-time sample. -/
noncomputable def auxiliarySignJitterLaw (x : ℕ → ℤ) (σ : ℤ) (n : ℕ) : ProbabilityMeasure ℝ :=
  meshJitterLaw n (auxiliarySignTimes x σ n)

theorem map_auxiliarySignJitterLaw_floor_time (x : ℕ → ℤ) (σ : ℤ) {n : ℕ}
    (hs : (auxiliarySignSteps x σ n).Nonempty) :
    (auxiliarySignJitterLaw x σ n).map (fun t : ℝ ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / n) =
      auxiliarySignTimeLaw x σ n := by
  have hn : 0 < n := by
    obtain ⟨i, hi⟩ := hs
    have hi' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hi).1
    omega
  have hs0 : (auxiliarySignTimes x σ n).Nonempty := by
    rw [← Finset.card_ne_zero, auxiliarySignTimes_card]
    exact hs.card_pos.ne'
  have hm : Measurable (fun t : ℝ ↦ ⌊(n : ℝ) * t⌋₊) :=
    (measurable_const.mul measurable_id).nat_floor
  apply ProbabilityMeasure.toMeasure_injective
  change (meshJitterLaw n (auxiliarySignTimes x σ n) : Measure ℝ).map
    (fun t : ℝ ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / n) = _
  rw [auxiliarySignTimeLaw_eq_uniform x σ hs,
    ← map_meshJitterLaw_floor (s := auxiliarySignTimes x σ n) hn (Finset.filter_subset _ _) hs0,
    Measure.map_map (measurable_of_countable (fun i : ℕ ↦ (i : ℝ) / n)) hm]
  rfl

/-- Jittering changes the selected time by at most one mesh width, so the
uniform weak limit from sign counting is preserved. -/
theorem tendsto_auxiliarySignJitterLaw_of_signMeasure {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    Tendsto (fun n ↦ auxiliarySignJitterLaw (x n) σ n) atTop (𝓝 profileProbabilityMeasure) := by
  let μ := fun n ↦ auxiliarySignJitterLaw (x n) σ n
  have hquant : Tendsto (fun n ↦ (μ n).map
      (fun t : ℝ ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / n)) atTop (𝓝 profileProbabilityMeasure) := by
    apply (tendsto_auxiliarySignTimeLaw_of_signMeasure h).congr'
    filter_upwards [eventually_auxiliarySignSteps_nonempty_of_signMeasure h] with n hn
    exact (map_auxiliarySignJitterLaw_floor_time (x n) σ hn).symm
  have hmap := tendsto_probabilityMap_of_error_probability μ
    (F := fun _ t ↦ t) (G := fun n t ↦ (⌊(n : ℝ) * t⌋₊ : ℝ) / n)
    (fun _ ↦ measurable_id)
    (fun n ↦ ((measurable_of_countable (fun i : ℕ ↦ (i : ℝ))).comp
      ((measurable_const.mul measurable_id).nat_floor)).div_const n) ?_ hquant
  · apply hmap.congr
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_id'
  · intro ε hε
    have hi : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply tendsto_const_nhds.congr'
    filter_upwards [hi.eventually_lt_const hε, eventually_gt_atTop 0,
      eventually_auxiliarySignTimes_nonempty_of_signMeasure h] with n hn hn0 hs
    have hzero : (μ n : Measure ℝ)
        {t | ε < dist t ((⌊(n : ℝ) * t⌋₊ : ℝ) / n)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [ae_mem_meshCells_meshJitterLaw hn0 (Finset.filter_subset _ _) hs] with t ht
      exact not_lt_of_ge ((dist_floor_mesh_lt hn0 ht).trans hn).le
    simp only [Measure.real, hzero, ENNReal.toReal_zero]

/-- The actual jittered sign-time laws are eventually bounded by four times
Lebesgue measure on the unit interval. The constant comes from sign density
one half, not an added assumption on the source profile. -/
theorem eventually_auxiliarySignJitterLaw_le {x : ℕ → ℕ → ℤ} {σ : ℤ}
    (h : Tendsto (fun n ↦ signTimeMeasure (x n) σ n) atTop (𝓝 profileFiniteMeasure)) :
    ∀ᶠ n in atTop, (auxiliarySignJitterLaw (x n) σ n : Measure ℝ) ≤
      (4 : ℝ≥0∞) • profileMeasure := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) / (auxiliarySignTimes (x n) σ n).card)
      atTop (𝓝 2) := by
    simpa only [inv_div, div_one] using
      (tendsto_auxiliarySignTimes_card_div h).inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  filter_upwards [ht.eventually_lt_const (by norm_num : (2 : ℝ) < 4),
    eventually_gt_atTop 0, eventually_auxiliarySignTimes_nonempty_of_signMeasure h] with n hc hn hs
  have hc' : (((n : ℝ≥0) / (auxiliarySignTimes (x n) σ n).card : ℝ≥0) : ℝ≥0∞) ≤ 4 := by
    exact_mod_cast hc.le
  exact (meshJitterLaw_le hn (Finset.filter_subset _ _) hs).trans (by
    gcongr
    simpa only [auxiliarySignTimes] using hc')

end Freezing2
