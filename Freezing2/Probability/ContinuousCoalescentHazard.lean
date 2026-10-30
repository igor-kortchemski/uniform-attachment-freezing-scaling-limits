module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

/-!
# Continuous coalescent survival and event-time normalization

This module starts the actual continuous-time coalescent construction. A
nonnegative locally integrable hazard has a normalized next-event law: its
continuous merger density plus survival at the lower time boundary has total
mass one. Endpoint survival will be retained as an atom, including the case
where the cumulative hazard diverges towards time zero.

The finite-interval identity below is proved from absolute continuity and the
Lebesgue differentiation theorem. No continuity of the hazard is assumed and
no genealogy density or normalization is taken as a premise.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2.ContinuousCoalescent

/-- Backward survival from upper time `b` down to time `t`. -/
noncomputable def survival (h : ℝ → ℝ) (b t : ℝ) : ℝ :=
  Real.exp (∫ u in b..t, h u)

theorem survival_eq_exp_neg (h : ℝ → ℝ) (b t : ℝ) :
    survival h b t = Real.exp (-(∫ u in t..b, h u)) := by
  rw [survival, intervalIntegral.integral_symm]

@[simp] theorem survival_self (h : ℝ → ℝ) (b : ℝ) : survival h b b = 1 := by
  simp [survival]

theorem survival_pos (h : ℝ → ℝ) (b t : ℝ) : 0 < survival h b t := Real.exp_pos _

theorem survival_le_one {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) {b t : ℝ} (ht : t ≤ b) :
    survival h b t ≤ 1 := by
  rw [survival_eq_exp_neg, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall ht h0)

/-- Survival increases with the lower time boundary, as it should for a
backward event clock. -/
theorem survival_mono {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {s t b : ℝ} (hst : s ≤ t) (htb : t ≤ b)
    (hInt : IntervalIntegrable h volume s b) : survival h b s ≤ survival h b t := by
  rw [survival_eq_exp_neg, survival_eq_exp_neg, Real.exp_le_exp]
  exact neg_le_neg (intervalIntegral.integral_mono_interval hst htb le_rfl
    (Eventually.of_forall h0) hInt)

/-- Exponentiation is one-Lipschitz on nonpositive arguments. -/
theorem exp_lipschitzOn_Iic_zero : LipschitzOnWith 1 Real.exp (Iic 0) := by
  apply (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
  intro x hx
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos x)] using Real.exp_le_one_iff.mpr hx

/-- The survival function is absolutely continuous on every interval on which
the hazard is integrable. -/
theorem survival_absolutelyContinuous {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {a b : ℝ} (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) :
    AbsolutelyContinuousOnInterval (survival h b) a b := by
  have hA := hInt.absolutelyContinuousOnInterval_intervalIntegral (c := b) (by simp)
  apply exp_lipschitzOn_Iic_zero.comp_absolutelyContinuousOnInterval _ hA
  intro t ht
  rw [uIcc_of_le hab] at ht
  change (∫ u in b..t, h u) ≤ 0
  rw [intervalIntegral.integral_symm]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall ht.2 h0)

/-- The exact event-density integral on a finite interval. This is the
normalization identity needed before defining the next-merger probability law. -/
theorem integral_survival_mul_hazard {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {a b : ℝ} (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) :
    (∫ t in a..b, survival h b t * h t) = 1 - survival h b a := by
  have hS := survival_absolutelyContinuous h0 hab hInt
  have hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (survival h b) (survival h b t * h t) t := by
    filter_upwards [hInt.ae_hasDerivAt_integral] with t ht htab
    exact (ht htab b (by simp)).exp
  calc
    (∫ t in a..b, survival h b t * h t) = ∫ t in a..b, deriv (survival h b) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with t ht htab
      exact (ht (uIoc_subset_uIcc htab)).deriv.symm
    _ = survival h b b - survival h b a := hS.integral_deriv_eq_sub
    _ = 1 - survival h b a := by rw [survival_self]

/-- An event before the cutoff has the hazard density; survival to the cutoff
is retained as an atom at that cutoff. -/
noncomputable def cutoffEventMeasure (h : ℝ → ℝ) (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity
      (fun t ↦ ENNReal.ofReal (survival h b t * h t)) +
    ENNReal.ofReal (survival h b a) • Measure.dirac a

/-- The hazard-density part has exactly the complementary survival mass. -/
theorem cutoff_density_mass {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {a b : ℝ} (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) :
    ((volume.restrict (Ioc a b)).withDensity
      (fun t ↦ ENNReal.ofReal (survival h b t * h t))) univ =
        ENNReal.ofReal (1 - survival h b a) := by
  have hSI := hInt.continuousOn_mul (survival_absolutelyContinuous h0 hab hInt).continuousOn
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hSI.left
      (Eventually.of_forall (fun t ↦ mul_nonneg (survival_pos h b t).le (h0 t))),
    ← intervalIntegral.integral_of_le hab, integral_survival_mul_hazard h0 hab hInt]

/-- Probability normalization is proved from the hazard, not postulated as a
condition on the next-event distribution. -/
theorem cutoffEventMeasure_univ {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t)
    {a b : ℝ} (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) :
    cutoffEventMeasure h a b univ = 1 := by
  rw [cutoffEventMeasure, Measure.add_apply, cutoff_density_mass h0 hab hInt, Measure.smul_apply]
  simp only [Measure.dirac_apply_of_mem (mem_univ a), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (survival_le_one h0 hab)) (survival_pos h b a).le]
  simp

/-- The cutoff atom is exactly the no-merger survival probability. -/
theorem cutoffEventMeasure_singleton_cutoff (h : ℝ → ℝ) (a b : ℝ) :
    cutoffEventMeasure h a b {a} = ENNReal.ofReal (survival h b a) := by
  simp [cutoffEventMeasure]

/-- The normalized finite-cutoff next-event law, with its actual survival atom. -/
noncomputable def cutoffEventLaw (h : ℝ → ℝ) (a b : ℝ) (h0 : ∀ t, 0 ≤ h t)
    (hab : a ≤ b) (hInt : IntervalIntegrable h volume a b) : ProbabilityMeasure ℝ :=
  ⟨cutoffEventMeasure h a b, ⟨cutoffEventMeasure_univ h0 hab hInt⟩⟩

end Freezing2.ContinuousCoalescent
