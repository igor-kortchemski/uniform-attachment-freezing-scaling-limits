module

public import Freezing2.Probability.ContinuousCoalescentHazard
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The zero-endpoint atom of the continuous coalescent clock

Positive cutoffs decrease to zero. Their survival probabilities have a limit,
and continuity from below for the hazard-density measure proves that this
limit is exactly the missing mass. This constructs the full next-event law
without assigning a totalized Bochner integral to a divergent endpoint hazard.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2.ContinuousCoalescent

/-- Positive cutoffs exhausting the interval above zero. -/
noncomputable def cutoffTime (b : ℝ) (n : ℕ) : ℝ := b / ((n : ℝ) + 1)

theorem cutoffTime_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < cutoffTime b n := by
  unfold cutoffTime
  positivity

theorem cutoffTime_le {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : cutoffTime b n ≤ b := by
  unfold cutoffTime
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  nlinarith [mul_nonneg hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem cutoffTime_antitone {b : ℝ} (hb : 0 ≤ b) : Antitone (cutoffTime b) := by
  intro n m hnm
  unfold cutoffTime
  apply div_le_div_of_nonneg_left hb (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

theorem tendsto_cutoffTime_zero (b : ℝ) : Tendsto (cutoffTime b) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The genuine zero-endpoint survival, defined by positive cutoffs. -/
noncomputable def endpointSurvival (h : ℝ → ℝ) (b : ℝ) : ℝ :=
  ⨅ n : ℕ, survival h b (cutoffTime b n)

theorem endpointSurvival_nonneg (h : ℝ → ℝ) (b : ℝ) : 0 ≤ endpointSurvival h b := by
  apply le_ciInf
  intro n
  exact (survival_pos h b _).le

theorem endpointSurvival_le_one (h : ℝ → ℝ) (b : ℝ) : endpointSurvival h b ≤ 1 := by
  have hbound := ciInf_le (f := fun n : ℕ ↦ survival h b (cutoffTime b n))
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (survival_pos h b _).le⟩ 0
  simpa only [endpointSurvival, cutoffTime, Nat.cast_zero, zero_add, div_one, survival_self] using hbound

/-- No integrability at zero is assumed: every positive cutoff is enough. -/
theorem tendsto_survival_cutoff {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b) :
    Tendsto (fun n ↦ survival h b (cutoffTime b n)) atTop (𝓝 (endpointSurvival h b)) := by
  apply tendsto_atTop_ciInf
  · intro n m hnm
    exact survival_mono h0 (cutoffTime_antitone hb.le hnm) (cutoffTime_le hb.le n)
      (hInt _ (cutoffTime_pos hb m) (cutoffTime_le hb.le m))
  · exact ⟨0, by rintro _ ⟨n, rfl⟩; exact (survival_pos h b _).le⟩

/-- The positive-cutoff intervals exhaust the whole positive part. -/
theorem iUnion_cutoffTime_Ioc {b : ℝ} (hb : 0 < b) :
    (⋃ n : ℕ, Ioc (cutoffTime b n) b) = Ioc 0 b := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact ⟨(cutoffTime_pos hb n).trans hn.1, hn.2⟩
  · intro ht
    obtain ⟨n, hn⟩ := ((tendsto_cutoffTime_zero b).eventually_lt_const ht.1).exists
    exact mem_iUnion.mpr ⟨n, hn, ht.2⟩

/-- Continuous event density above zero. -/
noncomputable def positiveEventMeasure (h : ℝ → ℝ) (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 b)).withDensity (fun t ↦ ENNReal.ofReal (survival h b t * h t))

/-- Its mass on a positive tail is the already proved finite-cutoff density mass. -/
theorem positiveEventMeasure_Ioc {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) :
    positiveEventMeasure h b (Ioc a b) = ENNReal.ofReal (1 - survival h b a) := by
  have hs : Ioc a b ⊆ Ioc 0 b := Ioc_subset_Ioc ha le_rfl
  calc
    _ = ((volume.restrict (Ioc a b)).withDensity
        (fun t ↦ ENNReal.ofReal (survival h b t * h t))) univ := by
      rw [positiveEventMeasure, withDensity_apply _ measurableSet_Ioc,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hs]
    _ = _ := cutoff_density_mass h0 hab hInt

theorem positiveEventMeasure_restrict_eq_self (h : ℝ → ℝ) (b : ℝ) :
    (positiveEventMeasure h b).restrict (Ioc 0 b) = positiveEventMeasure h b := by
  ext E hE
  rw [Measure.restrict_apply hE, positiveEventMeasure,
    withDensity_apply _ (hE.inter measurableSet_Ioc), withDensity_apply _ hE,
    Measure.restrict_restrict (hE.inter measurableSet_Ioc), Measure.restrict_restrict hE]
  simp only [inter_assoc, inter_self]

/-- The continuous part has exactly the mass complementary to endpoint survival. -/
theorem positiveEventMeasure_univ {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b) :
    positiveEventMeasure h b univ = ENNReal.ofReal (1 - endpointSurvival h b) := by
  have hmono : Monotone (fun n : ℕ ↦ Ioc (cutoffTime b n) b) := by
    intro n m hnm
    exact Ioc_subset_Ioc (cutoffTime_antitone hb.le hnm) le_rfl
  have hm := tendsto_measure_iUnion_atTop (μ := positiveEventMeasure h b) hmono
  rw [iUnion_cutoffTime_Ioc hb] at hm
  have he : positiveEventMeasure h b (Ioc 0 b) = positiveEventMeasure h b univ := by
    rw [← positiveEventMeasure_restrict_eq_self h b, Measure.restrict_apply_univ,
      Measure.restrict_apply_self]
  rw [he] at hm
  have hn : Tendsto (fun n ↦ positiveEventMeasure h b (Ioc (cutoffTime b n) b)) atTop
      (𝓝 (ENNReal.ofReal (1 - endpointSurvival h b))) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_survival_cutoff h0 hb hInt))
    apply ht.congr
    intro n
    exact (positiveEventMeasure_Ioc h0 (cutoffTime_pos hb n).le (cutoffTime_le hb.le n)
      (hInt _ (cutoffTime_pos hb n) (cutoffTime_le hb.le n))).symm
  exact tendsto_nhds_unique hm hn

/-- The complete backward event law, including the possibly positive atom at zero. -/
noncomputable def eventMeasure (h : ℝ → ℝ) (b : ℝ) : Measure ℝ :=
  positiveEventMeasure h b + ENNReal.ofReal (endpointSurvival h b) • Measure.dirac 0

theorem eventMeasure_univ {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b) :
    eventMeasure h b univ = 1 := by
  rw [eventMeasure, Measure.add_apply, positiveEventMeasure_univ h0 hb hInt, Measure.smul_apply]
  simp only [Measure.dirac_apply_of_mem (mem_univ (0 : ℝ)), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (endpointSurvival_le_one h b))
    (endpointSurvival_nonneg h b)]
  simp

noncomputable def eventLaw (h : ℝ → ℝ) (b : ℝ) (h0 : ∀ t, 0 ≤ h t) (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b) : ProbabilityMeasure ℝ :=
  ⟨eventMeasure h b, ⟨eventMeasure_univ h0 hb hInt⟩⟩

/-- Endpoint survival is an actual atom, not a totalized divergent integral. -/
theorem eventMeasure_singleton_zero (h : ℝ → ℝ) (b : ℝ) :
    eventMeasure h b {0} = ENNReal.ofReal (endpointSurvival h b) := by
  simp [eventMeasure, positiveEventMeasure]

/-- Infinite cumulative hazard forces the true endpoint survival to vanish. -/
theorem endpointSurvival_eq_zero_of_cumulative_tendsto {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b)
    (hdiv : Tendsto (fun n ↦ ∫ u in cutoffTime b n..b, h u) atTop atTop) :
    endpointSurvival h b = 0 := by
  have hz := Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  have hs : Tendsto (fun n ↦ survival h b (cutoffTime b n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, survival_eq_exp_neg] using hz
  exact tendsto_nhds_unique (tendsto_survival_cutoff h0 hb hInt) hs

/-- The source's divergent integral hypothesis is interpreted as an extended
nonnegative integral, so it does not collapse to zero under Bochner totalization. -/
theorem tendsto_cumulative_atTop_of_lintegral_eq_top {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b)
    (hdiv : (∫⁻ u in Ioc 0 b, ENNReal.ofReal (h u)) = ∞) :
    Tendsto (fun n ↦ ∫ u in cutoffTime b n..b, h u) atTop atTop := by
  have hmono : Monotone (fun n : ℕ ↦ Ioc (cutoffTime b n) b) := by
    intro n m hnm
    exact Ioc_subset_Ioc (cutoffTime_antitone hb.le hnm) le_rfl
  have hm := tendsto_measure_iUnion_atTop
    (μ := volume.withDensity (fun u ↦ ENNReal.ofReal (h u))) hmono
  rw [iUnion_cutoffTime_Ioc hb, withDensity_apply _ measurableSet_Ioc, hdiv] at hm
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  apply hm.congr
  intro n
  rw [Function.comp_apply, withDensity_apply _ measurableSet_Ioc,
    intervalIntegral.integral_of_le (cutoffTime_le hb.le n)]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hInt _ (cutoffTime_pos hb n) (cutoffTime_le hb.le n)).left
    (Eventually.of_forall h0)).symm

theorem endpointSurvival_eq_zero_of_lintegral_eq_top {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b)
    (hdiv : (∫⁻ u in Ioc 0 b, ENNReal.ofReal (h u)) = ∞) :
    endpointSurvival h b = 0 :=
  endpointSurvival_eq_zero_of_cumulative_tendsto h0 hb hInt
    (tendsto_cumulative_atTop_of_lintegral_eq_top h0 hb hInt hdiv)

/-- Under infinite cumulative hazard there is no residual no-merger atom. -/
theorem eventMeasure_singleton_zero_of_lintegral_eq_top {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {b : ℝ} (hb : 0 < b)
    (hInt : ∀ a, 0 < a → a ≤ b → IntervalIntegrable h volume a b)
    (hdiv : (∫⁻ u in Ioc 0 b, ENNReal.ofReal (h u)) = ∞) :
    eventMeasure h b {0} = 0 := by
  rw [eventMeasure_singleton_zero, endpointSurvival_eq_zero_of_lintegral_eq_top h0 hb hInt hdiv,
    ENNReal.ofReal_zero]

end Freezing2.ContinuousCoalescent
