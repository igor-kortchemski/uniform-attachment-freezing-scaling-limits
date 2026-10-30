module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.BernoulliArrayLimits

/-!
# Normalized limits from a Poisson-type MGF bound

This interface applies the analytic part of the height argument directly to a
random variable whose exponential moments have been computed. The moment bound
and concentration estimates are proved here. An application to the random tree
must prove the stated MGF estimate and exponential integrability for its actual
height law; neither is a substitute for constructing that law.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {m : ℝ}

/-- The same Bennett upper and lower tails follow from the full MGF estimate. -/
theorem bennett_tails_of_mgf_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | m + t < X ω} ≤ Real.exp (-m * bennettRate (t / m)) ∧
    μ.real {ω | X ω < m - t} ≤ Real.exp (-m * bennettRate (t / m)) := by
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by have := div_pos ht hm; linarith)
  constructor
  · calc
      μ.real {ω | m + t < X ω} ≤ μ.real {ω | m + t ≤ X ω} :=
        measureReal_mono (by
          intro ω hω
          change m + t < X ω at hω
          change m + t ≤ X ω
          exact hω.le) (measure_ne_top μ _)
      _ ≤ Real.exp (-θ * (m + t)) * mgf X μ θ :=
        measure_ge_le_exp_mul_mgf (m + t) hθ (h_int θ)
      _ ≤ Real.exp (-θ * (m + t)) * Real.exp (m * (Real.exp θ - 1)) :=
        mul_le_mul_of_nonneg_left (h_mgf θ) (Real.exp_pos _).le
      _ = Real.exp (-m * bennettRate (t / m)) := by
        rw [← Real.exp_add]
        congr 1
        exact bennett_exponent_identity hm ht
  · calc
      μ.real {ω | X ω < m - t} ≤ μ.real {ω | X ω ≤ m - t} :=
        measureReal_mono (by
          intro ω hω
          change X ω < m - t at hω
          change X ω ≤ m - t
          exact hω.le) (measure_ne_top μ _)
      _ ≤ Real.exp (-(-θ) * (m - t)) * mgf X μ (-θ) :=
        measure_le_le_exp_mul_mgf (m - t) (neg_nonpos.mpr hθ) (h_int (-θ))
      _ ≤ Real.exp (-(-θ) * (m - t)) * Real.exp (m * (Real.exp (-θ) - 1)) :=
        mul_le_mul_of_nonneg_left (h_mgf (-θ)) (Real.exp_pos _).le
      _ ≤ Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le hθ) hm.le
        nlinarith
      _ = Real.exp (-m * bennettRate (t / m)) := by
        congr 1
        exact bennett_exponent_identity hm ht

/-- Two-sided normalized concentration from an actual MGF estimate. -/
theorem normalized_deviation_le_of_mgf_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |X ω / m - 1|} ≤ 2 * Real.exp (-m * bennettRate (ε / 2)) := by
  let t : ℝ := (ε / 2) * m
  have ht : 0 < t := mul_pos (half_pos hε) hm
  obtain ⟨hu, hl⟩ := bennett_tails_of_mgf_bound h_int h_mgf hm ht
  have htm : t / m = ε / 2 := by dsimp [t]; field_simp [hm.ne']
  rw [htm] at hu hl
  have hsubset : {ω | ε ≤ |X ω / m - 1|} ⊆
      {ω | m + t < X ω} ∪ {ω | X ω < m - t} := by
    intro ω hω
    have heq : X ω / m - 1 = (X ω - m) / m := by field_simp [hm.ne']
    change ε ≤ |X ω / m - 1| at hω
    rw [heq, abs_div, abs_of_pos hm] at hω
    have hh := (le_div_iff₀ hm).mp hω
    rcases le_abs.mp hh with hh | hh
    · left
      change m + t < X ω
      dsimp [t]
      nlinarith [mul_pos hε hm]
    · right
      change X ω < m - t
      dsimp [t]
      nlinarith [mul_pos hε hm]
  calc
    μ.real {ω | ε ≤ |X ω / m - 1|} ≤
        μ.real ({ω | m + t < X ω} ∪ {ω | X ω < m - t}) :=
      measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ μ.real {ω | m + t < X ω} + μ.real {ω | X ω < m - t} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-m * bennettRate (ε / 2)) := by linarith

omit [IsProbabilityMeasure μ] in
/-- Normalizing preserves exponential integrability at every parameter. -/
theorem normalized_exp_integrable
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ) (θ : ℝ) :
    Integrable (fun ω ↦ Real.exp (θ * (X ω / m))) μ := by
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h_int (θ / m)

omit [IsProbabilityMeasure μ] in
/-- The MGF estimate gives a universal exponential-moment bound after normalization. -/
theorem normalized_exp_integral_le_of_mgf_bound
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 1 ≤ m) {θ : ℝ} (hθ : θ ≤ 1) :
    (∫ ω, Real.exp (θ * (X ω / m)) ∂μ) ≤ Real.exp (Real.exp 1 - 1) := by
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
    (∫ ω, Real.exp (θ * (X ω / m)) ∂μ) = mgf X μ (θ / m) := by
      simp only [mgf, div_mul_eq_mul_div, mul_div_assoc]
    _ ≤ Real.exp (m * (Real.exp (θ / m) - 1)) := h_mgf _
    _ ≤ Real.exp (Real.exp 1 - 1) := by
      apply Real.exp_le_exp.mpr
      have hmono : Real.exp (θ / m) ≤ Real.exp (1 / m) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hθ hmpos.le)
      have hh : Real.exp (θ / m) - 1 ≤ (Real.exp 1 - 1) / m := by linarith
      simpa only [mul_comm] using (le_div_iff₀ hmpos).mp hh

omit [IsProbabilityMeasure μ] in
/-- Actual exponential integrability and the MGF estimate give uniform real moments. -/
theorem normalized_moment_le_of_mgf_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 1 ≤ m) {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ 2 * q ^ q * Real.exp (Real.exp 1 - 1) := by
  have hpos : Integrable (fun ω ↦ Real.exp (X ω / m)) μ := by
    simpa only [one_mul] using normalized_exp_integrable h_int (m := m) 1
  have hneg : Integrable (fun ω ↦ Real.exp (-(X ω / m))) μ := by
    simpa only [neg_one_mul] using normalized_exp_integrable h_int (m := m) (-1)
  have hrpow : Integrable (fun ω ↦ |X ω / m| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq
    · simpa only [one_mul] using hpos
    · simpa only [neg_one_mul] using hneg
  have hbound : ∀ ω, |X ω / m| ^ q ≤ q ^ q *
      (Real.exp (X ω / m) + Real.exp (-(X ω / m))) := by
    intro ω
    have hb := rpow_abs_le_mul_max_exp_of_pos (X ω / m) hq (t := 1) zero_lt_one
    simp only [div_one, one_mul, neg_one_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq _))
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hup : (∫ ω, Real.exp (X ω / m) ∂μ) ≤ Real.exp (Real.exp 1 - 1) := by
    simpa only [one_mul] using normalized_exp_integral_le_of_mgf_bound h_mgf hm (θ := 1) le_rfl
  have hdown : (∫ ω, Real.exp (-(X ω / m)) ∂μ) ≤ Real.exp (Real.exp 1 - 1) := by
    simpa only [neg_one_mul] using
      normalized_exp_integral_le_of_mgf_bound h_mgf hm (θ := -1) (by norm_num)
  calc
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ ∫ ω, q ^ q *
        (Real.exp (X ω / m) + Real.exp (-(X ω / m))) ∂μ :=
      integral_mono hrpow ((hpos.add hneg).const_mul _) hbound
    _ = q ^ q * ((∫ ω, Real.exp (X ω / m) ∂μ) + ∫ ω, Real.exp (-(X ω / m)) ∂μ) := by
      rw [integral_const_mul, integral_add hpos hneg]
    _ ≤ 2 * q ^ q * Real.exp (Real.exp 1 - 1) := by
      have hqq : 0 ≤ q ^ q := Real.rpow_nonneg hq _
      nlinarith

omit [IsProbabilityMeasure μ] in
/-- Uniform bounds on all positive `Lq` norms, derived from the actual MGF estimate. -/
theorem normalized_eLpNorm_le_of_mgf_bound
    (hX : Measurable X)
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun ω ↦ X ω / m) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((2 * q ^ q * Real.exp (Real.exp 1 - 1)) ^ q⁻¹) := by
  have hZ : AEStronglyMeasurable (fun ω ↦ X ω / m) μ := by fun_prop
  have hrpow : Integrable (fun ω ↦ |X ω / m| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq.le
    · exact normalized_exp_integrable h_int 1
    · exact normalized_exp_integrable h_int (-1)
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hMem : MemLp (fun ω ↦ X ω / m) (ENNReal.ofReal q) μ :=
    (integrable_norm_rpow_iff hZ hq0 ENNReal.ofReal_ne_top).mp (by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using hrpow)
  rw [hMem.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (normalized_moment_le_of_mgf_bound h_int h_mgf hm hq.le) (inv_nonneg.mpr hq.le)

/-- The analytic limit theorem for the actual height laws. The probability spaces
may vary with the horizon, and every real exponent at least one is permitted. -/
theorem normalized_tendsto_Lp_of_mgf_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {Z : ∀ n, Ξ n → ℝ} {a : ℕ → ℝ}
    (hZ : ∀ n, Measurable (Z n))
    (h_int : ∀ n θ, Integrable (fun ω ↦ Real.exp (θ * Z n ω)) (ν n))
    (h_mgf : ∀ n θ, mgf (Z n) (ν n) θ ≤ Real.exp (a n * (Real.exp θ - 1)))
    (ha : Tendsto a atTop atTop) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / a n - 1)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal ((2 * (r + 1) ^ (r + 1) *
    Real.exp (Real.exp 1 - 1)) ^ (r + 1)⁻¹)
  have hq : 0 < r + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n ↦ by fun_prop)
    hr (lt_add_one r) (C := K + 1) (by finiteness)
  · filter_upwards [ha.eventually_ge_atTop 1] with n hn
    have hconst : eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
      simp
    calc
      _ ≤ eLpNorm (fun ω ↦ Z n ω / a n) (ENNReal.ofReal (r + 1)) (ν n) +
          eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) :=
        eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ r + 1 by linarith))
      _ ≤ K + 1 := by
        rw [hconst]
        exact add_le_add (normalized_eLpNorm_le_of_mgf_bound
          (hZ n) (h_int n) (h_mgf n) hn hq) le_rfl
  · intro ε hε
    apply (ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top (ν n) _)).mp
    have hg : 0 < bennettRate (ε / 2) := bennettRate_pos (half_pos hε)
    have he : Tendsto (fun n ↦ Real.exp (-a n * bennettRate (ε / 2))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hneg := tendsto_neg_atTop_atBot.comp (ha.atTop_mul_const hg)
      change Tendsto (fun n ↦ -(a n * bennettRate (ε / 2))) atTop atBot at hneg
      simpa only [neg_mul] using hneg
    have hb : Tendsto (fun n ↦ 2 * Real.exp (-a n * bennettRate (ε / 2)))
        atTop (𝓝 0) := by simpa using he.const_mul 2
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) ?_ hb
    filter_upwards [ha.eventually_gt_atTop 0] with n hn
    simpa only [Real.norm_eq_abs, measureReal_def] using
      normalized_deviation_le_of_mgf_bound (h_int n) (h_mgf n) hn hε

end Freezing1
