module

public import Freezing2.Probability.ContinuousCoalescentEndpoint
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Kernel.Basic

/-!
# Measurable next-event kernels for the continuous coalescent

The event laws already normalized from the locally integrable hazard vary
measurably with their time boundaries. This supplies actual Markov kernels,
including the zero-endpoint survival atom, for finite genealogy construction.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2.ContinuousCoalescent

/-- A measurable integrand gives a jointly measurable interval integral; no
integrability hypothesis is needed for this measurability statement. -/
theorem measurable_intervalIntegral {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (fun p : ℝ × ℝ ↦ ∫ u in p.1..p.2, h u) := by
  have hset : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ p.1.2} :=
    (measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hm := ((hh.comp measurable_snd).indicator hset).stronglyMeasurable.integral_prod_right'
    (ν := volume)
  have hI : Measurable (fun p : ℝ × ℝ ↦ ∫ u in Ioc p.1 p.2, h u) := by
    convert hm.measurable using 1
    ext p
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  exact hI.sub (hI.comp measurable_swap)

theorem measurable_survival {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (fun p : ℝ × ℝ ↦ survival h p.1 p.2) :=
  Real.continuous_exp.measurable.comp (measurable_intervalIntegral hh)

theorem measurable_endpointSurvival {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (endpointSurvival h) := by
  apply Measurable.iInf
  intro n
  exact (measurable_survival hh).comp
    (measurable_id.prodMk (measurable_id.div_const ((n : ℝ) + 1)))

/-- The continuous density on a varying interval is a measurable measure-valued
map. Its second boundary is also the upper survival boundary. -/
theorem measurable_cutoffDensity {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (fun p : ℝ × ℝ ↦ (volume.restrict (Ioc p.1 p.2)).withDensity
      (fun t ↦ ENNReal.ofReal (survival h p.2 t * h t))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hset : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.2 ∈ E ∧ p.1.1 < p.2 ∧ p.2 ≤ p.1.2} :=
    (hE.preimage measurable_snd).inter
      ((measurableSet_lt measurable_fst.fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.snd))
  have hw : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      ENNReal.ofReal (survival h p.1.2 p.2 * h p.2)) :=
    (((measurable_survival hh).comp (measurable_fst.snd.prodMk measurable_snd)).mul
      (hh.comp measurable_snd)).ennreal_ofReal
  have hm := (hw.indicator hset).lintegral_prod_right' (ν := volume)
  convert hm using 1
  ext p
  rw [withDensity_apply _ hE, Measure.restrict_restrict hE,
    ← lintegral_indicator (hE.inter measurableSet_Ioc)]
  rfl

theorem measurable_cutoffEventMeasure {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (fun p : ℝ × ℝ ↦ cutoffEventMeasure h p.1 p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hD := (Measure.measurable_coe hE).comp (measurable_cutoffDensity hh)
  have hS := ((measurable_survival hh).comp measurable_swap).ennreal_ofReal
  have hA : Measurable (fun p : ℝ × ℝ ↦ Measure.dirac p.1 E) :=
    (Measure.measurable_coe hE).comp (Measure.measurable_dirac.comp measurable_fst)
  convert hD.add (hS.mul hA) using 1
  funext p
  simp only [cutoffEventMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.mul_apply, Function.comp_apply, Prod.fst_swap, Prod.snd_swap]

theorem measurable_positiveEventMeasure {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (positiveEventMeasure h) := by
  have he : positiveEventMeasure h = (fun p : ℝ × ℝ ↦ (volume.restrict (Ioc p.1 p.2)).withDensity
      (fun t ↦ ENNReal.ofReal (survival h p.2 t * h t))) ∘ (fun b : ℝ ↦ ((0 : ℝ), b)) := by
    funext b
    rfl
  rw [he]
  exact (measurable_cutoffDensity hh).comp (measurable_const.prodMk measurable_id)

theorem measurable_eventMeasure {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (eventMeasure h) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hD := (Measure.measurable_coe hE).comp (measurable_positiveEventMeasure hh)
  have hS := (measurable_endpointSurvival hh).ennreal_ofReal
  convert hD.add (hS.mul_const (Measure.dirac (0 : ℝ) E)) using 1
  funext b
  simp only [eventMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Pi.add_apply, Function.comp_apply]

/-- A valid next-event window may stop at a positive next birth or at zero.
The current upper time is strictly between zero and one. -/
def EventWindow := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ 0 < p.2 ∧ p.2 < 1}

noncomputable instance : MeasurableSpace EventWindow := Subtype.instMeasurableSpace

/-- The actual next-event kernel uses positive-cutoff survival at a birth and
the genuine endpoint survival at zero. -/
noncomputable def nextEventKernel (h : ℝ → ℝ) (hh : Measurable h) : Kernel EventWindow ℝ where
  toFun w := if w.val.1 = 0 then eventMeasure h w.val.2
    else cutoffEventMeasure h w.val.1 w.val.2
  measurable' := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (measurable_subtype_coe.fst) measurable_const
    · exact (measurable_eventMeasure hh).comp measurable_subtype_coe.snd
    · exact (measurable_cutoffEventMeasure hh).comp measurable_subtype_coe

theorem nextEventKernel_isMarkov (h : ℝ → ℝ) (hh : Measurable h)
    (h0 : ∀ t, 0 ≤ h t)
    (hInt : ∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable h volume a b) :
    IsMarkovKernel (nextEventKernel h hh) := by
  constructor
  intro w
  constructor
  change (if w.val.1 = 0 then eventMeasure h w.val.2
    else cutoffEventMeasure h w.val.1 w.val.2) univ = 1
  split_ifs with hw
  · exact eventMeasure_univ h0 w.property.2.2.1
      (fun a ha hab ↦ hInt a w.val.2 ha hab w.property.2.2.2)
  · exact cutoffEventMeasure_univ h0 w.property.2.1
      (hInt _ _ (lt_of_le_of_ne w.property.1 (Ne.symm hw))
        w.property.2.1 w.property.2.2.2)

end Freezing2.ContinuousCoalescent
