module

public import Freezing2.Analysis.LocalSquareProfiles
public import Freezing2.Analysis.SignMeasures
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local L1 convergence controls errors sampled in the unit interval

The limiting reciprocal-square profile need only be locally integrable in the
open unit interval. Small endpoint strips and Markov's inequality transfer
local L1 convergence to convergence in probability, also under uniformly
Lebesgue-dominated varying sampling laws.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace Freezing2

/-- Real-valued Markov bound for the strict absolute-error event. -/
theorem measureReal_abs_gt_le_integral_div {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {f : A → ℝ}
    (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε < |f x|} ≤ (∫ x, |f x| ∂μ) / ε := by
  apply (le_div_iff₀ hε).mpr
  calc
    μ.real {x | ε < |f x|} * ε ≤ μ.real {x | ε ≤ |f x|} * ε :=
      mul_le_mul_of_nonneg_right (measureReal_mono (μ := μ) (by
        intro x hx
        change ε < |f x| at hx
        exact hx.le)) hε.le
    _ ≤ ∫ x, |f x| ∂μ := by
      simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall (fun x ↦ abs_nonneg (f x))) hf.abs ε

/-- The two endpoint strips have exactly their Lebesgue length. -/
theorem profileMeasure_real_compl_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    profileMeasure.real (Icc a b)ᶜ = 1 - (b - a) := by
  have hU : profileMeasure.real univ = 1 := profileFiniteMeasure_mass
  rw [measureReal_compl measurableSet_Icc, hU]
  congr 1
  change (volume.restrict (Icc (0 : ℝ) 1)).real (Icc a b) = b - a
  rw [measureReal_restrict_apply measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc ha hb), Real.volume_real_Icc_of_le hab]

/-- Local integral absolute error on every interior interval is enough for
convergence in probability under the unit-interval reference measure. -/
theorem tendsto_profile_error_probability_of_local_l1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hInt : ∀ a b, 0 < a → a < b → b < 1 →
      ∀ n, IntegrableOn (fun t ↦ f n t - g t) (Icc a b) volume)
    (hL1 : ∀ a b, 0 < a → a < b → b < 1 →
      Tendsto (fun n ↦ ∫ t in Icc a b, |f n t - g t|) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ profileMeasure.real {t | ε < |f n t - g t|}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  let δ : ℝ := min (η / 8) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδsmall : 2 * δ ≤ η / 4 := by
    have := min_le_left (η / 8) (1 / 4)
    dsimp [δ]
    linarith
  have hab : δ < 1 - δ := by linarith
  have hb : 1 - δ < 1 := by linarith
  have hμK : profileMeasure.restrict (Icc δ (1 - δ)) =
      volume.restrict (Icc δ (1 - δ)) := profileMeasure_restrict_Icc hδ.le hb.le
  have ht : Tendsto (fun n ↦ (∫ t in Icc δ (1 - δ), |f n t - g t|) / ε)
      atTop (𝓝 0) := by simpa using (hL1 δ (1 - δ) hδ hab hb).div_const ε
  filter_upwards [ht.eventually_lt_const (by linarith : (0 : ℝ) < η / 2)] with n hn
  have hlocal : (profileMeasure.restrict (Icc δ (1 - δ))).real
      {t | ε < |f n t - g t|} ≤
        (∫ t in Icc δ (1 - δ), |f n t - g t|) / ε := by
    rw [hμK]
    exact measureReal_abs_gt_le_integral_div (hInt δ (1 - δ) hδ hab hb n) hε
  have hbound : profileMeasure.real {t | ε < |f n t - g t|} ≤
      profileMeasure.real (Icc δ (1 - δ))ᶜ +
        (profileMeasure.restrict (Icc δ (1 - δ))).real {t | ε < |f n t - g t|} := by
    rw [measureReal_restrict_apply' (μ := profileMeasure)
      (s := Icc δ (1 - δ)) (t := {t | ε < |f n t - g t|}) measurableSet_Icc]
    calc
      profileMeasure.real {t | ε < |f n t - g t|} ≤
          profileMeasure.real ((Icc δ (1 - δ))ᶜ ∪
            ({t | ε < |f n t - g t|} ∩ Icc δ (1 - δ))) :=
        measureReal_mono (μ := profileMeasure) (by
          intro t ht
          by_cases htk : t ∈ Icc δ (1 - δ)
          · exact Or.inr ⟨ht, htk⟩
          · exact Or.inl htk)
      _ ≤ _ := measureReal_union_le (μ := profileMeasure) _ _
  rw [profileMeasure_real_compl_Icc hδ.le hab.le hb.le] at hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- Uniform domination of measures gives the corresponding real event bound. -/
theorem measureReal_le_of_measure_le_smul {A : Type*} [MeasurableSpace A]
    {μ ν : Measure A} [IsFiniteMeasure μ] {c : ℝ≥0}
    (hν : ν ≤ (c : ℝ≥0∞) • μ) (E : Set A) :
    ν.real E ≤ (c : ℝ) * μ.real E := by
  have hfin : ((c : ℝ≥0∞) • μ) E ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top μ E)
  have he := ENNReal.toReal_mono hfin (hν E)
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    Measure.real] using he

/-- A reference error probability tending to zero also tends to zero under
any eventually uniformly dominated family of sampling measures. -/
theorem tendsto_error_probability_of_dominated {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {ν : ℕ → Measure A} {c : ℝ≥0}
    (hdom : ∀ᶠ n in atTop, ν n ≤ (c : ℝ≥0∞) • μ)
    {E : ℕ → Set A} (hE : Tendsto (fun n ↦ μ.real (E n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (ν n).real (E n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _
    (by simpa using hE.const_mul (c : ℝ))
  filter_upwards [hdom] with n hn
  exact measureReal_le_of_measure_le_smul hn (E n)

end Freezing2
