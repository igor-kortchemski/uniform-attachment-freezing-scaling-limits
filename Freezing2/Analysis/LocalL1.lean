module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local consequences of convergence in integral absolute error

The reciprocal profile hypothesis in the source is convergence in `L¹`.
These general lemmas transfer that convergence to integrals over fixed sets
and record strict positivity of the limiting integral. They do not assume or
prove a scaling estimate for the driving walk.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

variable {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Restricting to a set cannot increase the error controlled by the global
integral of the absolute difference. No regularity of the set is required. -/
theorem abs_setIntegral_sub_le_integral_abs_sub {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (s : Set Ω) :
    |(∫ x in s, f x ∂μ) - ∫ x in s, g x ∂μ| ≤ ∫ x, |f x - g x| ∂μ := by
  rw [← integral_sub hf.restrict hg.restrict]
  calc
    |∫ x in s, f x - g x ∂μ| ≤ ∫ x in s, |f x - g x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, |f x - g x| ∂μ :=
      setIntegral_le_integral (hf.sub hg).abs (ae_of_all μ fun x ↦ abs_nonneg _)

/-- Convergence in integral absolute error implies convergence of the integrals
on every fixed subset. Integrability is explicit to exclude totalized integrals. -/
theorem tendsto_setIntegral_of_l1 {f : κ → Ω → ℝ} {g : Ω → ℝ} {l : Filter κ}
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ)
    (hL1 : Tendsto (fun i ↦ ∫ x, |f i x - g x| ∂μ) l (𝓝 0)) (s : Set Ω) :
    Tendsto (fun i ↦ ∫ x in s, f i x ∂μ) l (𝓝 (∫ x in s, g x ∂μ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun i ↦ abs_nonneg _)
    (fun i ↦ abs_setIntegral_sub_le_integral_abs_sub (hf i) hg s) hL1

/-- A positive almost-everywhere integrable function has strictly positive
integral on any nonzero measure space. -/
theorem integral_pos_of_ae_pos {g : Ω → ℝ} (hg : Integrable g μ)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (hμ : μ ≠ 0) : 0 < ∫ x, g x ∂μ := by
  let : NeZero μ := ⟨hμ⟩
  have hnonneg : 0 ≤ᵐ[μ] g := hpos.mono fun x hx ↦ hx.le
  have hI : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hnonneg
  by_contra hnot
  have hzero : ∫ x, g x ∂μ = 0 := le_antisymm (le_of_not_gt hnot) hI
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hg).mp hzero
  obtain ⟨x, hp, hx⟩ := (hpos.and hz).exists
  exact hp.ne' hx

/-- The integral of an almost-everywhere positive integrable function over a
set of positive measure is strictly positive. -/
theorem setIntegral_pos_of_ae_pos {g : Ω → ℝ} (hg : Integrable g μ)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) {s : Set Ω} (hs : μ s ≠ 0) :
    0 < ∫ x in s, g x ∂μ :=
  integral_pos_of_ae_pos hg.restrict (ae_restrict_of_ae hpos)
    (mt Measure.restrict_eq_zero.mp hs)

/-- An event implying a vanishing upper bound for a quantity converging to a
strictly positive number is eventually impossible. The conditional estimate
may itself hold only eventually. -/
theorem eventually_not_of_tendsto_pos_of_bound {A B : κ → ℝ} {l : Filter κ}
    {c : ℝ} (hA : Tendsto A l (𝓝 c)) (hc : 0 < c)
    (hB : Tendsto B l (𝓝 0)) (H : κ → Prop)
    (hbound : ∀ᶠ i in l, H i → A i ≤ B i) : ∀ᶠ i in l, ¬ H i := by
  filter_upwards [hB.eventually_lt hA hc, hbound] with i hlt hle
  exact fun hi ↦ (not_le_of_gt hlt) (hle hi)

end Freezing2
