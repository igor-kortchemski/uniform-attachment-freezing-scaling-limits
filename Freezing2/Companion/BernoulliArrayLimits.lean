module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.BernoulliLimits

/-!
# Bernoulli limits on varying probability spaces

The law of the random tree changes with the horizon. The results here permit
a different sample space and probability measure in every row. Thus the analytic
limit argument does not require a separately constructed common coupling.

The proof splits each error at a fixed positive cutoff and uses Hölder for the
large-error part. Uniform higher moments come from the proved Bernoulli MGF
bound, not from a hypothesis asserting the desired height estimate.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

/-- Cut an `Lp` norm into a bounded part and a higher-moment tail. -/
theorem eLpNorm_le_cutoff_add_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {p q ε : ℝ}
    (hp : 1 ≤ p) (hpq : p < q) (hε : 0 ≤ ε) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε +
      eLpNorm f (ENNReal.ofReal q) μ * μ {ω | ε ≤ ‖f ω‖} ^ (1 / p - 1 / q) := by
  let s : Set Ω := {ω | ε ≤ ‖f ω‖}
  have hs : MeasurableSet s := measurableSet_le measurable_const hf.norm
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := hp0.trans hpq
  have hsplit : f = sᶜ.indicator f + s.indicator f := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  have hlo : eLpNorm (sᶜ.indicator f) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
    have hb : ∀ᵐ ω ∂μ, ‖sᶜ.indicator f ω‖ ≤ ε := by
      apply ae_of_all
      intro ω
      by_cases hω : ω ∈ s
      · simp [hω, hε]
      · have : ‖f ω‖ < ε := lt_of_not_ge hω
        simpa [hω] using this.le
    simpa using eLpNorm_le_of_ae_bound (hf.aestronglyMeasurable.indicator hs.compl) hb
  have hhi : eLpNorm (s.indicator f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal q) μ * μ s ^ (1 / p - 1 / q) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    calc
      eLpNorm f (ENNReal.ofReal p) (μ.restrict s) ≤
          eLpNorm f (ENNReal.ofReal q) (μ.restrict s) * μ s ^ (1 / p - 1 / q) := by
        simpa only [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le,
          Measure.restrict_apply_univ] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (ENNReal.ofReal_le_ofReal hpq.le) hf.aestronglyMeasurable.restrict
      _ ≤ eLpNorm f (ENNReal.ofReal q) μ * μ s ^ (1 / p - 1 / q) :=
        mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  calc
    eLpNorm f (ENNReal.ofReal p) μ =
        eLpNorm (sᶜ.indicator f + s.indicator f) (ENNReal.ofReal p) μ :=
      congrArg (fun g : Ω → ℝ ↦ eLpNorm g (ENNReal.ofReal p) μ) hsplit
    _ ≤ eLpNorm (sᶜ.indicator f) (ENNReal.ofReal p) μ +
        eLpNorm (s.indicator f) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le (by simpa using ENNReal.ofReal_le_ofReal hp)
    _ ≤ _ := add_le_add hlo hhi

section VaryingMeasures

variable {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
  {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]

/-- Convergence in probability and an eventual bounded higher moment imply
`Lp` convergence even when the sample spaces and measures vary with `n`. -/
theorem tendsto_eLpNorm_of_tail_and_higher_moment
    {f : ∀ n, Ξ n → ℝ} (hf : ∀ n, Measurable (f n))
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ᶠ n in atTop, eLpNorm (f n) (ENNReal.ofReal q) (ν n) ≤ C)
    (htail : ∀ ε > 0, Tendsto (fun n ↦ ν n {ω | ε ≤ ‖f n ω‖}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n) (ENNReal.ofReal p) (ν n)) atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 < 1 / p - 1 / q :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hp0 hpq)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (2 : ℝ≥0∞)) (by norm_num) hδ.ne'
  have hεreal : (0 : ℝ) < ε := hε
  have hεenn : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hsmall : Tendsto (fun n ↦ C * ν n {ω | (ε : ℝ) ≤ ‖f n ω‖} ^
      (1 / p - 1 / q)) atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hr).comp (htail ε hεreal)
  filter_upwards [hbound, ENNReal.tendsto_nhds_zero.mp hsmall ε hεenn] with n hn hsmalln
  calc
    eLpNorm (f n) (ENNReal.ofReal p) (ν n) ≤ ENNReal.ofReal ε +
        eLpNorm (f n) (ENNReal.ofReal q) (ν n) *
          ν n {ω | (ε : ℝ) ≤ ‖f n ω‖} ^ (1 / p - 1 / q) :=
      eLpNorm_le_cutoff_add_tail (hf n) hp hpq hεreal.le
    _ ≤ (ε : ℝ≥0∞) + ε := by
      simp only [ENNReal.ofReal_coe_nnreal]
      exact add_le_add le_rfl ((mul_le_mul' hn le_rfl).trans hsmalln)
    _ ≤ δ := by
      have heq : (ε : ℝ≥0∞) + ε = ε * 2 := by rw [mul_two]
      exact heq ▸ hεδ.le

variable {ι : Type*}

/-- Probability convergence for independent Bernoulli arrays on varying spaces. -/
theorem bernoulli_normalized_tail_tendsto
    {Y : ∀ n, ι → Ξ n → ℝ} {p : ℕ → ι → unitInterval}
    (hY : ∀ n i, Measurable (Y n i)) (h_indep : ∀ n, iIndepFun (Y n) (ν n))
    (hLaw : ∀ n i, HasLaw (Y n i) (bernoulliMeasure (1 : ℝ) 0 (p n i)) (ν n))
    (s : ℕ → Finset ι)
    (hm : Tendsto (fun n ↦ ∑ i ∈ s n, (p n i : ℝ)) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ ν n {ω |
      ε ≤ |(∑ i ∈ s n, Y n i ω) / (∑ i ∈ s n, (p n i : ℝ)) - 1|}) atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top (ν n) _)).mp
  have hg : 0 < bennettRate (ε / 2) := bennettRate_pos (half_pos hε)
  have he : Tendsto (fun n ↦ Real.exp (-(∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hneg := tendsto_neg_atTop_atBot.comp (hm.atTop_mul_const hg)
    change Tendsto (fun n ↦ -((∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop atBot at hneg
    simpa only [neg_mul] using hneg
  have hb : Tendsto (fun n ↦ 2 * Real.exp (-(∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop (𝓝 0) := by simpa using he.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) ?_ hb
  filter_upwards [hm.eventually_gt_atTop 0] with n hn
  exact bernoulli_normalized_deviation_le (hY n) (h_indep n) (hLaw n) (s n) hn hε

/-- All finite real `Lp` limits for normalized Bernoulli sums, with a different
probability measure and sample space allowed at every horizon. -/
theorem bernoulli_normalized_tendsto_Lp_varying
    {Y : ∀ n, ι → Ξ n → ℝ} {p : ℕ → ι → unitInterval}
    (hY : ∀ n i, Measurable (Y n i)) (h_indep : ∀ n, iIndepFun (Y n) (ν n))
    (hLaw : ∀ n i, HasLaw (Y n i) (bernoulliMeasure (1 : ℝ) 0 (p n i)) (ν n))
    (s : ℕ → Finset ι)
    (hm : Tendsto (fun n ↦ ∑ i ∈ s n, (p n i : ℝ)) atTop atTop)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ (∑ i ∈ s n, Y n i ω) / (∑ i ∈ s n, (p n i : ℝ)) - 1)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal ((2 * (r + 1) ^ (r + 1) *
    Real.exp (Real.exp 1 - 1)) ^ (r + 1)⁻¹)
  have hq : 0 < r + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n ↦ by fun_prop)
    hr (lt_add_one r) (C := K + 1) (by finiteness)
  · filter_upwards [hm.eventually_ge_atTop 1] with n hn
    have hconst : eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
      simp
    calc
      _ ≤ eLpNorm (fun ω ↦ (∑ i ∈ s n, Y n i ω) / (∑ i ∈ s n, (p n i : ℝ)))
            (ENNReal.ofReal (r + 1)) (ν n) +
          eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) :=
        eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ r + 1 by linarith))
      _ ≤ K + 1 := by
        rw [hconst]
        exact add_le_add (bernoulli_normalized_eLpNorm_le
          (hY n) (h_indep n) (hLaw n) (s n) hn hq) le_rfl
  · intro ε hε
    simpa only [Real.norm_eq_abs] using bernoulli_normalized_tail_tendsto hY h_indep hLaw s hm hε

end VaryingMeasures

end Freezing1
