module

public import Freezing2.Probability.ContinuousCoalescentEndpoint
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite and zero total rates for the continuous coalescent

Finite integrated hazard leaves a strictly positive no-merger atom at zero.
Zero or one current clusters have zero total hazard and a deterministic clock.
The actual cluster hazard is the number of unordered pairs times the squared
reciprocal profile, with no additional regularity assumption on that profile.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2.ContinuousCoalescent

/-- With integrability at zero, the genuine endpoint agrees with the ordinary
survival formula. The separate divergent case is in `ContinuousCoalescentEndpoint`. -/
theorem endpointSurvival_eq_survival_of_integrable {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b) (hInt : IntervalIntegrable h volume 0 b) :
    endpointSurvival h b = survival h b 0 := by
  have hS := (survival_absolutelyContinuous h0 hb.le hInt).continuousOn
  have hcut : Tendsto (cutoffTime b) atTop (𝓝[uIcc 0 b] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_cutoffTime_zero b, Eventually.of_forall fun n ↦ ?_⟩
    rw [uIcc_of_le hb.le]
    exact ⟨(cutoffTime_pos hb n).le, cutoffTime_le hb.le n⟩
  have hc := (hS 0 (by simp)).tendsto.comp hcut
  exact tendsto_nhds_unique
    (tendsto_survival_cutoff h0 hb (fun a ha hab ↦
      hInt.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hb.le]; exact Icc_subset_Icc ha.le le_rfl))) hc

/-- The printed exponential survival formula is valid when its integral is finite. -/
theorem endpointSurvival_eq_exp_neg_of_integrable {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b) (hInt : IntervalIntegrable h volume 0 b) :
    endpointSurvival h b = Real.exp (-(∫ t in 0..b, h t)) := by
  rw [endpointSurvival_eq_survival_of_integrable h0 hb hInt, survival_eq_exp_neg]

theorem endpointSurvival_pos_of_integrable {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b) (hInt : IntervalIntegrable h volume 0 b) :
    0 < endpointSurvival h b := by
  rw [endpointSurvival_eq_survival_of_integrable h0 hb hInt]
  exact survival_pos _ _ _

/-- A finite cumulative hazard leaves a genuinely positive atom at time zero. -/
theorem eventMeasure_singleton_zero_pos_of_integrable {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b) (hInt : IntervalIntegrable h volume 0 b) :
    0 < eventMeasure h b {0} := by
  rw [eventMeasure_singleton_zero]
  exact ENNReal.ofReal_pos.mpr (endpointSurvival_pos_of_integrable h0 hb hInt)

@[simp] theorem survival_zero (b t : ℝ) : survival (fun _ ↦ 0) b t = 1 := by
  simp [survival]

@[simp] theorem endpointSurvival_zero (b : ℝ) : endpointSurvival (fun _ ↦ 0) b = 1 := by
  simp [endpointSurvival]

@[simp] theorem cutoffEventMeasure_zero (a b : ℝ) :
    cutoffEventMeasure (fun _ ↦ 0) a b = Measure.dirac a := by
  simp [cutoffEventMeasure]

@[simp] theorem eventMeasure_zero (b : ℝ) : eventMeasure (fun _ ↦ 0) b = Measure.dirac 0 := by
  simp [eventMeasure, positiveEventMeasure]

/-- The total merger rate of `m` clusters. Here `g` is the reciprocal source profile. -/
noncomputable def clusterHazard (g : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (m.choose 2 : ℝ) * g t ^ 2

theorem clusterHazard_nonneg (g : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    0 ≤ clusterHazard g m t := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem measurable_clusterHazard {g : ℝ → ℝ} (hg : Measurable g) (m : ℕ) :
    Measurable (clusterHazard g m) := (hg.pow_const 2).const_mul _

/-- The paper's local square-integrability assumption supplies all finite windows. -/
theorem intervalIntegrable_clusterHazard {g : ℝ → ℝ}
    (h2 : ∀ a b, 0 < a → a < b → b < 1 → IntegrableOn (fun t ↦ g t ^ 2) (Icc a b) volume)
    (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable (clusterHazard g m) volume a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact IntervalIntegrable.refl
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      (h2 a b ha hab hb)).const_mul _

/-- Zero or one cluster cannot merge; this case must not sample an empty pair set. -/
theorem clusterHazard_eq_zero_of_le_one (g : ℝ → ℝ) {m : ℕ} (hm : m ≤ 1) :
    clusterHazard g m = fun _ ↦ 0 := by
  funext t
  simp only [clusterHazard, Nat.choose_eq_zero_of_lt (by omega : m < 2), Nat.cast_zero, zero_mul]

theorem cutoffEventMeasure_clusterHazard_le_one (g : ℝ → ℝ) {m : ℕ} (hm : m ≤ 1)
    (a b : ℝ) : cutoffEventMeasure (clusterHazard g m) a b = Measure.dirac a := by
  rw [clusterHazard_eq_zero_of_le_one g hm, cutoffEventMeasure_zero]

theorem eventMeasure_clusterHazard_le_one (g : ℝ → ℝ) {m : ℕ} (hm : m ≤ 1)
    (b : ℝ) : eventMeasure (clusterHazard g m) b = Measure.dirac 0 := by
  rw [clusterHazard_eq_zero_of_le_one g hm, eventMeasure_zero]

end Freezing2.ContinuousCoalescent
