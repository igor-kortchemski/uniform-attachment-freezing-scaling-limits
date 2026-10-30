module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.BernoulliConcentration
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Limits of normalized Bernoulli sums

These are probability-theoretic dependencies of Theorem `thm:height` (I).
The identification of the height of a uniform active vertex with the Bernoulli
sum remains a separate obligation. No assertion here assumes that tree law.

The moment proof applies to every real exponent. It uses a uniform exponential
moment bound, Hölder's inequality, and Vitali convergence. It does not verify
the manuscript's repeated-integration-by-parts argument for real powers.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The exact strict two-sided bound used in the proof of Theorem `thm:height` (I). -/
theorem bernoulli_normalized_strict_deviation_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε < |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1|} ≤
      2 * Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate ε) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  let a : ℝ := ε * m
  have hm0 : m ≠ 0 := hm.ne'
  have ha : 0 < a := mul_pos hε hm
  have hdiv : a / m = ε := by dsimp [a]; field_simp [hm0]
  have hupper := bernoulli_sum_upper_tail hY h_indep hLaw s hm ha
  have hlower := bernoulli_sum_lower_tail hY h_indep hLaw s hm ha
  change μ.real {ω | m + a < ∑ i ∈ s, Y i ω} ≤ Real.exp (-m * bennettRate (a / m)) at hupper
  change μ.real {ω | (∑ i ∈ s, Y i ω) < m - a} ≤ Real.exp (-m * bennettRate (a / m)) at hlower
  rw [hdiv] at hupper hlower
  have hsubset : {ω | ε < |(∑ i ∈ s, Y i ω) / m - 1|} ⊆
      {ω | m + a < ∑ i ∈ s, Y i ω} ∪ {ω | (∑ i ∈ s, Y i ω) < m - a} := by
    intro ω hω
    change ε < |(∑ i ∈ s, Y i ω) / m - 1| at hω
    have heq : (∑ i ∈ s, Y i ω) / m - 1 = ((∑ i ∈ s, Y i ω) - m) / m := by
      field_simp [hm0]
    rw [heq, abs_div, abs_of_pos hm] at hω
    have hh := (lt_div_iff₀ hm).mp hω
    rcases lt_abs.mp hh with hh | hh
    · left
      change m + a < ∑ i ∈ s, Y i ω
      dsimp [a] at *
      linarith
    · right
      change (∑ i ∈ s, Y i ω) < m - a
      dsimp [a] at *
      linarith
  calc
    μ.real {ω | ε < |(∑ i ∈ s, Y i ω) / m - 1|} ≤
        μ.real ({ω | m + a < ∑ i ∈ s, Y i ω} ∪ {ω | (∑ i ∈ s, Y i ω) < m - a}) :=
      measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ μ.real {ω | m + a < ∑ i ∈ s, Y i ω} +
        μ.real {ω | (∑ i ∈ s, Y i ω) < m - a} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-m * bennettRate ε) := by linarith

/-- A weak-threshold form, convenient for the definition of convergence in
measure. It follows from the exact strict bound at half the threshold. -/
theorem bernoulli_normalized_deviation_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1|} ≤
      2 * Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (ε / 2)) := by
  refine (measureReal_mono (s₂ := {ω | ε / 2 <
    |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)) - 1|})
    (fun ω hω ↦ (half_lt_self hε).trans_le hω) (measure_ne_top μ _)).trans ?_
  exact bernoulli_normalized_strict_deviation_le hY h_indep hLaw s hm (half_pos hε)

/-- Normalized independent Bernoulli sums converge in probability when their
means tend to infinity. Independence is required only within each row. -/
theorem bernoulli_normalized_tendstoInMeasure
    {Y : ℕ → ι → Ω → ℝ} {p : ℕ → ι → unitInterval}
    (hY : ∀ n i, Measurable (Y n i)) (h_indep : ∀ n, iIndepFun (Y n) μ)
    (hLaw : ∀ n i, HasLaw (Y n i) (bernoulliMeasure (1 : ℝ) 0 (p n i)) μ)
    (s : ℕ → Finset ι)
    (hm : Tendsto (fun n ↦ ∑ i ∈ s n, (p n i : ℝ)) atTop atTop) :
    TendstoInMeasure μ
      (fun n ω ↦ (∑ i ∈ s n, Y n i ω) / (∑ i ∈ s n, (p n i : ℝ))) atTop
      (fun _ ↦ (1 : ℝ)) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hg : 0 < bennettRate (ε / 2) := bennettRate_pos (half_pos hε)
  have he : Tendsto (fun n ↦ Real.exp (-(∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hmul := hm.atTop_mul_const hg
    have hneg := tendsto_neg_atTop_atBot.comp hmul
    change Tendsto (fun n ↦ -((∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop atBot at hneg
    simpa only [neg_mul] using hneg
  have hb : Tendsto (fun n ↦ 2 * Real.exp (-(∑ i ∈ s n, (p n i : ℝ)) *
      bennettRate (ε / 2))) atTop (𝓝 0) := by simpa using he.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hb
  filter_upwards [hm.eventually_gt_atTop 0] with n hn
  simpa only [Real.norm_eq_abs] using
    bernoulli_normalized_deviation_le (hY n) (h_indep n) (hLaw n) (s n) hn hε

/-- Exponentials of every normalized Bernoulli sum are integrable, even when
the denominator is zero under the usual totalized division convention. -/
theorem bernoulli_normalized_exp_integrable
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (θ : ℝ) :
    Integrable (fun ω ↦ Real.exp (θ *
      ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ))))) μ := by
  have h := h_indep.integrable_exp_mul_sum hY
    (s := s) (t := θ / (∑ i ∈ s, (p i : ℝ)))
    (fun i _ ↦ integrable_exp_mul_bernoulli (hLaw i) _)
  simpa only [Finset.sum_apply, div_mul_eq_mul_div, mul_div_assoc] using h

omit [IsProbabilityMeasure μ] in
/-- A uniform exponential-moment bound once the Bernoulli mean is at least one. -/
theorem bernoulli_normalized_exp_integral_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 1 ≤ ∑ i ∈ s, (p i : ℝ)) {θ : ℝ} (hθ : θ ≤ 1) :
    (∫ ω, Real.exp (θ *
      ((∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)))) ∂μ) ≤
      Real.exp (Real.exp 1 - 1) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have ht0 : 0 ≤ 1 / m := by positivity
  have ht1 : 1 / m ≤ 1 := (div_le_one hmpos).mpr hm
  have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 (1 / m))
  have he : Real.exp (1 / m) ≤ 1 + (Real.exp 1 - 1) / m := by
    calc
      Real.exp (1 / m) ≤ (1 - 1 / m) * 1 + (1 / m) * Real.exp 1 := by
        simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] using hc
      _ = 1 + (Real.exp 1 - 1) / m := by ring
  calc
    (∫ ω, Real.exp (θ * ((∑ i ∈ s, Y i ω) / m)) ∂μ) =
        mgf (∑ i ∈ s, Y i) μ (θ / m) := by
      simp only [mgf, Finset.sum_apply, div_mul_eq_mul_div, mul_div_assoc]
    _ ≤ Real.exp (m * (Real.exp (θ / m) - 1)) :=
      mgf_sum_bernoulli_le hY h_indep hLaw s _
    _ ≤ Real.exp (Real.exp 1 - 1) := by
      apply Real.exp_le_exp.mpr
      have hmono : Real.exp (θ / m) ≤ Real.exp (1 / m) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hθ hmpos.le)
      have hh : Real.exp (θ / m) - 1 ≤ (Real.exp 1 - 1) / m := by linarith
      have := (le_div_iff₀ hmpos).mp hh
      simpa only [mul_comm] using this

/-- All real positive moments of the normalized sum admit one bound independent
of the number of summands once its mean is at least one. -/
theorem bernoulli_normalized_moment_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 1 ≤ ∑ i ∈ s, (p i : ℝ)) {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, |(∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ))| ^ q ∂μ) ≤
      2 * q ^ q * Real.exp (Real.exp 1 - 1) := by
  let Z : Ω → ℝ := fun ω ↦ (∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ))
  have hpos : Integrable (fun ω ↦ Real.exp (Z ω)) μ := by
    simpa only [one_mul] using bernoulli_normalized_exp_integrable hY h_indep hLaw s 1
  have hneg : Integrable (fun ω ↦ Real.exp (-Z ω)) μ := by
    simpa only [neg_one_mul] using bernoulli_normalized_exp_integrable hY h_indep hLaw s (-1)
  have hrpow : Integrable (fun ω ↦ |Z ω| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq
    · simpa only [one_mul] using hpos
    · simpa only [neg_one_mul] using hneg
  have hbound : ∀ ω, |Z ω| ^ q ≤ q ^ q * (Real.exp (Z ω) + Real.exp (-Z ω)) := by
    intro ω
    have hb := rpow_abs_le_mul_max_exp_of_pos (Z ω) hq (t := 1) zero_lt_one
    simp only [div_one, one_mul, neg_one_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq _))
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hup : (∫ ω, Real.exp (Z ω) ∂μ) ≤ Real.exp (Real.exp 1 - 1) := by
    simpa only [one_mul] using bernoulli_normalized_exp_integral_le hY h_indep hLaw s hm (θ := 1) le_rfl
  have hdown : (∫ ω, Real.exp (-Z ω) ∂μ) ≤ Real.exp (Real.exp 1 - 1) := by
    simpa only [neg_one_mul] using
      bernoulli_normalized_exp_integral_le hY h_indep hLaw s hm (θ := -1) (by norm_num)
  calc
    (∫ ω, |Z ω| ^ q ∂μ) ≤ ∫ ω, q ^ q * (Real.exp (Z ω) + Real.exp (-Z ω)) ∂μ :=
      integral_mono hrpow ((hpos.add hneg).const_mul _) hbound
    _ = q ^ q * ((∫ ω, Real.exp (Z ω) ∂μ) + ∫ ω, Real.exp (-Z ω) ∂μ) := by
      rw [integral_const_mul, integral_add hpos hneg]
    _ ≤ 2 * q ^ q * Real.exp (Real.exp 1 - 1) := by
      have hqq : 0 ≤ q ^ q := Real.rpow_nonneg hq _
      nlinarith

omit [IsProbabilityMeasure μ] in
/-- A bounded higher moment supplies uniform integrability by Hölder's
inequality on sets of small measure. -/
theorem unifIntegrable_of_uniform_eLpNorm_bound
    {f : ℕ → Ω → ℝ} {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ C) :
    UnifIntegrable f (ENNReal.ofReal p) μ := by
  have hq : 0 < q := hp.trans hpq
  let r : ℝ := 1 / p - 1 / q
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hp hpq)
  unfold UnifIntegrable
  apply tendsto_nhds_bot_mono
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hr)
  apply Eventually.of_forall
  intro ε
  simp only [iSup_le_iff]
  intro n s hs
  calc
    eLpNorm (f n) (ENNReal.ofReal p) (μ.restrict s) ≤
        eLpNorm (f n) (ENNReal.ofReal q) (μ.restrict s) * μ s ^ r := by
      simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le,
        Measure.restrict_apply_univ] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (ENNReal.ofReal_le_ofReal hpq.le) (hf n).restrict
    _ ≤ C * ε ^ r := by
      apply mul_le_mul'
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hbound n)
      · exact ENNReal.rpow_le_rpow hs hr.le

/-- Uniform bounds for every finite positive `Lq` norm of normalized Bernoulli
sums whose mean is at least one. -/
theorem bernoulli_normalized_eLpNorm_le
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 1 ≤ ∑ i ∈ s, (p i : ℝ)) {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun ω ↦ (∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ)))
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((2 * q ^ q * Real.exp (Real.exp 1 - 1)) ^ q⁻¹) := by
  let Z : Ω → ℝ := fun ω ↦ (∑ i ∈ s, Y i ω) / (∑ i ∈ s, (p i : ℝ))
  have hZ : AEStronglyMeasurable Z μ := by dsimp [Z]; fun_prop
  have hrpow : Integrable (fun ω ↦ |Z ω| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq.le
    · exact bernoulli_normalized_exp_integrable hY h_indep hLaw s 1
    · exact bernoulli_normalized_exp_integrable hY h_indep hLaw s (-1)
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hMem : MemLp Z (ENNReal.ofReal q) μ :=
    (integrable_norm_rpow_iff hZ hq0 ENNReal.ofReal_ne_top).mp (by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using hrpow)
  rw [hMem.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (bernoulli_normalized_moment_le hY h_indep hLaw s hm hq.le) (inv_nonneg.mpr hq.le)

/-- Every finite real `Lp` convergence for normalized independent Bernoulli
triangular arrays whose means tend to infinity. There is no independence
assumption between different rows and no unproved moment-bound hypothesis. -/
theorem bernoulli_normalized_tendsto_Lp
    {Y : ℕ → ι → Ω → ℝ} {p : ℕ → ι → unitInterval}
    (hY : ∀ n i, Measurable (Y n i)) (h_indep : ∀ n, iIndepFun (Y n) μ)
    (hLaw : ∀ n i, HasLaw (Y n i) (bernoulliMeasure (1 : ℝ) 0 (p n i)) μ)
    (s : ℕ → Finset ι)
    (hm : Tendsto (fun n ↦ ∑ i ∈ s n, (p n i : ℝ)) atTop atTop)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm
      (fun ω ↦ (∑ i ∈ s n, Y n i ω) / (∑ i ∈ s n, (p n i : ℝ)) - 1)
      (ENNReal.ofReal r) μ) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hm.eventually_ge_atTop 1)
  let Z : ℕ → Ω → ℝ := fun n ω ↦
    (∑ i ∈ s (n + N), Y (n + N) i ω) / (∑ i ∈ s (n + N), (p (n + N) i : ℝ))
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hq : 0 < r + 1 := by linarith
  have hmeas : ∀ n, AEStronglyMeasurable (Z n) μ := by
    intro n
    dsimp [Z]
    fun_prop
  have hui : UnifIntegrable Z (ENNReal.ofReal r) μ := by
    apply unifIntegrable_of_uniform_eLpNorm_bound hrpos (lt_add_one r) hmeas
      (C := ENNReal.ofReal ((2 * (r + 1) ^ (r + 1) *
        Real.exp (Real.exp 1 - 1)) ^ (r + 1)⁻¹)) ENNReal.ofReal_ne_top
    intro n
    exact bernoulli_normalized_eLpNorm_le (hY _) (h_indep _) (hLaw _) (s _)
      (hN _ (Nat.le_add_left _ _)) hq
  have hconv : TendstoInMeasure μ Z atTop (fun _ ↦ (1 : ℝ)) := by
    apply bernoulli_normalized_tendstoInMeasure
      (fun n ↦ hY (n + N)) (fun n ↦ h_indep (n + N)) (fun n ↦ hLaw (n + N))
      (fun n ↦ s (n + N))
    exact hm.comp (tendsto_add_atTop_nat N)
  have hLp := tendsto_Lp_finite_of_tendstoInMeasure
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal r by simpa using ENNReal.ofReal_le_ofReal hr)
    ENNReal.ofReal_ne_top hmeas (memLp_const (1 : ℝ)) hui hconv
  exact (tendsto_add_atTop_iff_nat N).mp hLp

end Freezing1
