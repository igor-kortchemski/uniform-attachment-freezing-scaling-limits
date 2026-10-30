module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.MGFLimits
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Real moments for normalized nonnegative maxima

A bound `E exp X ≤ exp (B * m)` implies `E exp (X / m) ≤ exp B` for `m ≥ 1`
by Jensen's inequality. This handles the vertex-count prefactor in the
maximum-height MGF bound when its logarithm is negligible relative to `m`.
The convergence theorem below still requires the probability tails and this
eventual exponential bound to be proved for the actual random maximum.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {m B : ℝ}

/-- Jensen removes the growing exponent from the exponential moment. -/
theorem normalized_exp_integral_le_of_exp_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m)) :
    (∫ ω, Real.exp (X ω / m) ∂μ) ≤ Real.exp B := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmi0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hmpos.le
  have hmi1 : m⁻¹ ≤ 1 := (inv_le_one₀ hmpos).mpr hm
  have hp : Integrable (fun ω ↦ Real.exp (X ω)) μ := by simpa using h_int 1
  have hpNorm : Integrable (fun ω ↦ (Real.exp (X ω)) ^ m⁻¹) μ := by
    simpa only [← Real.exp_mul, one_mul, div_eq_mul_inv] using
      normalized_exp_integrable h_int (m := m) 1
  have hj := (Real.concaveOn_rpow hmi0 hmi1).le_map_integral
    (Real.continuous_rpow_const hmi0).continuousOn isClosed_Ici
    (ae_of_all μ (fun ω ↦ (Real.exp_pos (X ω)).le)) hp hpNorm
  calc
    (∫ ω, Real.exp (X ω / m) ∂μ) = ∫ ω, (Real.exp (X ω)) ^ m⁻¹ ∂μ := by
      simp only [← Real.exp_mul, div_eq_mul_inv]
    _ ≤ (∫ ω, Real.exp (X ω) ∂μ) ^ m⁻¹ := hj
    _ ≤ (Real.exp (B * m)) ^ m⁻¹ := by
      apply Real.rpow_le_rpow (integral_nonneg fun ω ↦ (Real.exp_pos (X ω)).le) ?_ hmi0
      simpa only [mgf, one_mul] using hbound
    _ = Real.exp B := by
      rw [← Real.exp_mul]
      congr 1
      field_simp

/-- Nonnegativity supplies the opposite exponential moment bound. -/
theorem normalized_neg_exp_integral_le_one
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hm : 0 < m) :
    (∫ ω, Real.exp (-(X ω / m)) ∂μ) ≤ 1 := by
  have hi : Integrable (fun ω ↦ Real.exp (-(X ω / m))) μ := by
    simpa only [neg_one_mul] using normalized_exp_integrable h_int (m := m) (-1)
  have hb : ∀ᵐ ω ∂μ, Real.exp (-(X ω / m)) ≤ (1 : ℝ) := by
    filter_upwards [hX] with ω hω
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hω hm.le))
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) hb

/-- Every nonnegative real moment is bounded uniformly from the exponential bound. -/
theorem normalized_moment_le_of_exp_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m))
    {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ q ^ q * (Real.exp B + 1) := by
  have hpos : Integrable (fun ω ↦ Real.exp (X ω / m)) μ := by
    simpa only [one_mul] using normalized_exp_integrable h_int (m := m) 1
  have hneg : Integrable (fun ω ↦ Real.exp (-(X ω / m))) μ := by
    simpa only [neg_one_mul] using normalized_exp_integrable h_int (m := m) (-1)
  have hrpow : Integrable (fun ω ↦ |X ω / m| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq
    · simpa only [one_mul] using hpos
    · simpa only [neg_one_mul] using hneg
  have hpoint : ∀ ω, |X ω / m| ^ q ≤ q ^ q *
      (Real.exp (X ω / m) + Real.exp (-(X ω / m))) := by
    intro ω
    have hb := rpow_abs_le_mul_max_exp_of_pos (X ω / m) hq (t := 1) zero_lt_one
    simp only [div_one, one_mul, neg_one_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq _))
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hup := normalized_exp_integral_le_of_exp_bound h_int hm hbound
  have hdown := normalized_neg_exp_integral_le_one h_int hX (lt_of_lt_of_le zero_lt_one hm)
  calc
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ ∫ ω, q ^ q *
        (Real.exp (X ω / m) + Real.exp (-(X ω / m))) ∂μ :=
      integral_mono hrpow ((hpos.add hneg).const_mul _) hpoint
    _ = q ^ q * ((∫ ω, Real.exp (X ω / m) ∂μ) + ∫ ω, Real.exp (-(X ω / m)) ∂μ) := by
      rw [integral_const_mul, integral_add hpos hneg]
    _ ≤ q ^ q * (Real.exp B + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hup hdown) (Real.rpow_nonneg hq _)

/-- The corresponding uniform bound for finite positive `Lq` norms. -/
theorem normalized_eLpNorm_le_of_exp_bound
    (h_meas : Measurable X)
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m))
    {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun ω ↦ X ω / m) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((q ^ q * (Real.exp B + 1)) ^ q⁻¹) := by
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
    (normalized_moment_le_of_exp_bound h_int hX hm hbound hq.le) (inv_nonneg.mpr hq.le)

/-- Exponential moments upgrade the already proved probability convergence of
nonnegative normalized variables to every finite real `Lp` convergence. -/
theorem normalized_tendsto_Lp_of_eventual_exp_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {Z : ∀ n, Ξ n → ℝ} {a : ℕ → ℝ} {B : ℝ}
    (hZ : ∀ n, Measurable (Z n))
    (h_int : ∀ n θ, Integrable (fun ω ↦ Real.exp (θ * Z n ω)) (ν n))
    (h_nonneg : ∀ n, ∀ᵐ ω ∂ν n, 0 ≤ Z n ω)
    (h_exp : ∀ᶠ n in atTop, mgf (Z n) (ν n) 1 ≤ Real.exp (B * a n))
    (ha : Tendsto a atTop atTop)
    (h_tail : ∀ ε > 0, Tendsto (fun n ↦ ν n {ω | ε ≤ |Z n ω / a n - 1|})
      atTop (𝓝 0)) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / a n - 1)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (((r + 1) ^ (r + 1) *
    (Real.exp B + 1)) ^ (r + 1)⁻¹)
  have hq : 0 < r + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n ↦ by fun_prop)
    hr (lt_add_one r) (C := K + 1) (by finiteness)
  · filter_upwards [ha.eventually_ge_atTop 1, h_exp] with n hn hexp
    have hconst : eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
      simp
    calc
      _ ≤ eLpNorm (fun ω ↦ Z n ω / a n) (ENNReal.ofReal (r + 1)) (ν n) +
          eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) :=
        eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ r + 1 by linarith))
      _ ≤ K + 1 := by
        rw [hconst]
        exact add_le_add (normalized_eLpNorm_le_of_exp_bound
          (hZ n) (h_int n) (h_nonneg n) hn hexp hq) le_rfl
  · intro ε hε
    simpa only [Real.norm_eq_abs] using h_tail ε hε

end Freezing1
