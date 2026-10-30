module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Transferring normalized Lᵖ convergence between deterministic scales

The probability spaces may depend on the horizon. A deterministic coefficient
converging to `c` transfers `Yₙ → 1` in Lᵖ to `bₙYₙ → c` in Lᵖ. The result
includes exponent infinity and introduces no rate assumption. The second
formulation changes from a normalization `aₙ` to a normalization `sₙ`.

These are analytic transfer lemmas for the main height result. They do not
establish the required Lᵖ concentration of the tree height itself.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ENNReal

namespace Freezing2

/-- An explicit Lᵖ bound for multiplication by a deterministic coefficient.
On a probability space the norm of the constant error is its scalar norm. -/
theorem eLpNorm_scaled_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (Y : Ω → ℝ) (b c : ℝ) :
    eLpNorm (fun ω ↦ b * Y ω - c) p μ ≤
      ‖b‖ₑ * eLpNorm (fun ω ↦ Y ω - 1) p μ + ‖b - c‖ₑ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp)
  have he : (fun ω ↦ b * Y ω - c) =
      b • (fun ω ↦ Y ω - 1) + (fun _ : Ω ↦ b - c) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (b • (fun ω ↦ Y ω - 1)) p μ +
        eLpNorm (fun _ : Ω ↦ b - c) p μ := eLpNorm_add_le hp
    _ = _ := by
      rw [eLpNorm_const_smul, eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero μ)]
      simp

/-- Deterministic scaling preserves Lᵖ convergence, even when the probability
spaces vary with `n`. Only the given norm convergence is required; no bounded
rate or finite-horizon integrability assumption is inserted. -/
theorem tendsto_eLpNorm_scaled_sub
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Y : (n : ℕ) → Ω n → ℝ}
    {b : ℕ → ℝ} {c : ℝ} (hb : Tendsto b atTop (𝓝 c))
    (hY : Tendsto (fun n ↦ eLpNorm (fun ω ↦ Y n ω - 1) p (μ n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ b n * Y n ω - c) p (μ n)) atTop (𝓝 0) := by
  have hprod : Tendsto
      (fun n ↦ ‖b n‖ₑ * eLpNorm (fun ω ↦ Y n ω - 1) p (μ n)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul hb.enorm (Or.inr ENNReal.zero_ne_top) hY
      (Or.inr (enorm_ne_top : ‖c‖ₑ ≠ ⊤))
  have hconstant : Tendsto (fun n ↦ ‖b n - c‖ₑ) atTop (𝓝 0) := by
    simpa using (hb.sub_const c).enorm
  have hbound : Tendsto
      (fun n ↦ ‖b n‖ₑ * eLpNorm (fun ω ↦ Y n ω - 1) p (μ n) + ‖b n - c‖ₑ)
      atTop (𝓝 0) := by simpa using hprod.add hconstant
  exact tendsto_const_nhds.squeeze hbound (fun _ ↦ bot_le)
    (fun n ↦ eLpNorm_scaled_sub_le (μ n) hp (Y n) (b n) c)

/-- Change the deterministic normalization of a family of random variables.
Both denominators are required to be nonzero only eventually, as is sufficient
for an asymptotic statement. -/
theorem tendsto_eLpNorm_change_normalization
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Z : (n : ℕ) → Ω n → ℝ}
    {a s : ℕ → ℝ} {c : ℝ}
    (ha : ∀ᶠ n in atTop, a n ≠ 0) (hs : ∀ᶠ n in atTop, s n ≠ 0)
    (hscale : Tendsto (fun n ↦ a n / s n) atTop (𝓝 c))
    (hZ : Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / a n - 1) p (μ n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / s n - c) p (μ n)) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_scaled_sub hp hscale hZ
  apply h.congr'
  filter_upwards [ha, hs] with n han hsn
  apply congrArg (fun f : Ω n → ℝ ↦ eLpNorm f p (μ n))
  funext ω
  field_simp [han, hsn]

/-- The finite real-exponent version of deterministic Lᵖ rescaling. -/
theorem tendsto_eLpNorm_scaled_sub_ofReal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {p : ℝ} (hp : 1 ≤ p) {Y : (n : ℕ) → Ω n → ℝ}
    {b : ℕ → ℝ} {c : ℝ} (hb : Tendsto b atTop (𝓝 c))
    (hY : Tendsto (fun n ↦ eLpNorm (fun ω ↦ Y n ω - 1) (ENNReal.ofReal p) (μ n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ b n * Y n ω - c) (ENNReal.ofReal p) (μ n))
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_scaled_sub _ hb hY
  simpa using ENNReal.ofReal_le_ofReal hp

end Freezing2
