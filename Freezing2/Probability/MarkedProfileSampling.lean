module

public import Freezing2.Probability.DominatedWeakConvergence
public import Freezing2.Probability.LocalProfileInMeasure
public import Freezing2.Probability.WeakPerturbation
public import Freezing2.Probability.BranchLengthLimit
public import Freezing2.Analysis.SquareCorrection

/-!
# Joint convergence of sampled times and measurable profile marks

Local L1 convergence, common Lebesgue domination of the sampling laws, and
weak convergence of their times imply joint weak convergence of time and mark.
An almost-everywhere measurable limiting profile suffices: a measurable
representative is used only inside the proof and the stated limiting law
retains the original profile.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2

/-- Mark convergence with a measurable limiting profile. No pointwise or
continuity assumption on either limiting mark or approximating marks is used. -/
theorem tendsto_marked_profile_of_local_l1
    {νs : ℕ → ProbabilityMeasure ℝ} {c : ℝ≥0} (hc : 1 ≤ c)
    (hweak : Tendsto νs atTop (𝓝 profileProbabilityMeasure))
    (hdom : ∀ᶠ n in atTop, (νs n : Measure ℝ) ≤ (c : ℝ≥0∞) • profileMeasure)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hInt : ∀ a b, 0 < a → a < b → b < 1 →
      ∀ n, IntegrableOn (fun t ↦ f n t - g t) (Icc a b) volume)
    (hL1 : ∀ a b, 0 < a → a < b → b < 1 →
      Tendsto (fun n ↦ ∫ t in Icc a b, |f n t - g t|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (νs n).map (fun t ↦ (t, f n t))) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, g t)))) := by
  have hν : (profileProbabilityMeasure : Measure ℝ) ≤ (c : ℝ≥0∞) • profileMeasure := by
    change profileMeasure ≤ (c : ℝ≥0∞) • profileMeasure
    calc
      profileMeasure = (1 : ℝ≥0∞) • profileMeasure := (one_smul _ _).symm
      _ ≤ _ := by gcongr; exact_mod_cast hc
  have hlim := tendsto_probabilityMap_of_weak_of_dominated hweak hdom hν
    (measurable_id.prodMk hg)
  apply tendsto_probabilityMap_of_error_probability νs
    (F := fun n t ↦ (t, f n t)) (G := fun _ t ↦ (t, g t))
    (fun n ↦ measurable_id.prodMk (hf n)) (fun _ ↦ measurable_id.prodMk hg) ?_ hlim
  intro ε hε
  have he := tendsto_error_probability_of_dominated hdom
    (tendsto_profile_error_probability_of_local_l1 hInt hL1 hε)
  have hmax (r : ℝ) : max 0 |r| = |r| := max_eq_right (abs_nonneg r)
  simpa only [Prod.dist_eq, dist_self, Real.dist_eq, hmax] using he

/-- Almost-everywhere measurable profiles give the same conclusion, retaining
the original function in the limiting pushforward law. -/
theorem tendsto_marked_profile_of_local_l1_ae
    {νs : ℕ → ProbabilityMeasure ℝ} {c : ℝ≥0} (hc : 1 ≤ c)
    (hweak : Tendsto νs atTop (𝓝 profileProbabilityMeasure))
    (hdom : ∀ᶠ n in atTop, (νs n : Measure ℝ) ≤ (c : ℝ≥0∞) • profileMeasure)
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, Measurable (f n))
    (hg : AEMeasurable g profileMeasure)
    (hInt : ∀ a b, 0 < a → a < b → b < 1 →
      ∀ n, IntegrableOn (fun t ↦ f n t - g t) (Icc a b) volume)
    (hL1 : ∀ a b, 0 < a → a < b → b < 1 →
      Tendsto (fun n ↦ ∫ t in Icc a b, |f n t - g t|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (νs n).map (fun t ↦ (t, f n t))) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, g t)))) := by
  let G := hg.mk g
  have hG : Measurable G := hg.measurable_mk
  have he : g =ᵐ[profileMeasure] G := hg.ae_eq_mk
  have heK {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
      g =ᵐ[volume.restrict (Icc a b)] G := by
    rw [← profileMeasure_restrict_Icc ha.le hb.le]
    exact ae_restrict_of_ae he
  have hIntG : ∀ a b, 0 < a → a < b → b < 1 →
      ∀ n, IntegrableOn (fun t ↦ f n t - G t) (Icc a b) volume := by
    intro a b ha hab hb n
    exact (hInt a b ha hab hb n).congr
      ((heK ha hb).mono (fun t ht ↦ congrArg (fun r : ℝ ↦ f n t - r) ht))
  have hL1G : ∀ a b, 0 < a → a < b → b < 1 →
      Tendsto (fun n ↦ ∫ t in Icc a b, |f n t - G t|) atTop (𝓝 0) := by
    intro a b ha hab hb
    apply (hL1 a b ha hab hb).congr
    intro n
    exact integral_congr_ae
      ((heK ha hb).mono (fun t ht ↦ congrArg (fun r : ℝ ↦ |f n t - r|) ht))
  have hmap : profileProbabilityMeasure.map (fun t ↦ (t, G t)) =
      profileProbabilityMeasure.map (fun t ↦ (t, g t)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_congr (he.symm.mono (fun t ht ↦ Prod.ext rfl ht))
  rw [← hmap]
  exact tendsto_marked_profile_of_local_l1 hc hweak hdom hf hG hIntG hL1G

/-- The source's shifted reciprocal-square profiles can be marked under any
uniformly dominated sampling laws converging weakly to uniform time. -/
theorem tendsto_marked_shiftedSquareProfile
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α)
    (hL1 : HasL1ReciprocalProfile x α g) (h2 : HasLocalSquareMomentProfile x α g)
    (hg0 : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {νs : ℕ → ProbabilityMeasure ℝ} {c : ℝ≥0} (hc : 1 ≤ c)
    (hweak : Tendsto νs atTop (𝓝 profileProbabilityMeasure))
    (hdom : ∀ᶠ n in atTop, (νs n : Measure ℝ) ≤ (c : ℝ≥0∞) • profileMeasure) :
    Tendsto (fun n ↦ (νs n).map (fun t ↦ (t, shiftedSquareProfile x α n t))) atTop
      (𝓝 (profileProbabilityMeasure.map (fun t ↦ (t, (g t) ^ 2)))) := by
  apply tendsto_marked_profile_of_local_l1_ae hc hweak hdom
    (fun n ↦ measurable_stepProfile
      (fun i ↦ ((n : ℝ) ^ α) ^ 2 /
        ((activeCount (x n) i : ℝ) * ((activeCount (x n) i : ℝ) + 1))) n)
    (hL1.1.aemeasurable.pow_const 2)
  · intro a b ha hab hb n
    exact (integrableOn_shiftedSquareProfile x α n ha.le hb.le).sub (h2 a b ha hab hb).1
  · intro a b ha hab hb
    exact tendsto_integral_abs_shiftedSquareProfile_sub_local hx hα hL1 h2 hg0 ha hab hb

end Freezing2
