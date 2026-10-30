module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Ring

/-!
# Uniformly small integrals on short intervals

The inclusive mesh sum in Lemma `lem:hnalpha(v)` integrates through
`(b+1)/n`, whereas its stated limiting integral stops at `b/n`. Absolute
continuity of the integral makes the intervening one-cell integral small
uniformly over every endpoint whose cell stays in a fixed interior interval.
The estimates below require no sign or boundedness assumption on the function.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- Absolute continuity of a real integral in an explicit epsilon-delta form.
The same measure threshold works simultaneously for every set. -/
theorem exists_pos_setIntegral_abs_lt_of_measure_lt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ENNReal, 0 < δ ∧ ∀ s : Set Ω,
      μ s < δ → |∫ x in s, f x ∂μ| < ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (f := fun x ↦ ‖f x‖ₑ) (ne_of_lt hf.2)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  refine ⟨δ, hδ, fun s hs ↦ ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mp
  have hnorm := enorm_integral_le_lintegral_enorm (μ := μ.restrict s) f
  rw [Real.enorm_eq_ofReal_abs] at hnorm
  exact hnorm.trans_lt (hbound s hs)

/-- A vanishing common upper bound on set measures gives a simultaneous bound
on every corresponding set integral. The universal set quantifier follows the
eventual horizon quantifier. -/
theorem eventually_uniform_setIntegral_abs_lt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) {r : ℕ → ENNReal}
    (hr : Tendsto r atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Set Ω,
      μ s ≤ r n → |∫ x in s, f x ∂μ| < ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_setIntegral_abs_lt_of_measure_lt hf hε
  filter_upwards [hr.eventually_lt_const hδ] with n hn
  exact fun s hs ↦ hbound s (hs.trans_lt hn)

/-- Integrals over every subinterval of length at most `1/n` are uniformly small
inside any fixed region on which the function is integrable. -/
theorem eventually_uniform_short_interval_integral_abs_lt
    {f : ℝ → ℝ} {K : Set ℝ} (hf : IntegrableOn f K volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℝ, Icc a b ⊆ K → b - a ≤ 1 / (n : ℝ) →
      |∫ t in Icc a b, f t| < ε := by
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_uniform_setIntegral_abs_lt hf hr hε] with n hn
  intro a b hsub hlen
  have hmeasure : (volume.restrict K) (Icc a b) ≤ ENNReal.ofReal (1 / (n : ℝ)) := by
    calc
      _ ≤ volume (Icc a b) := Measure.restrict_apply_le K (Icc a b)
      _ = ENNReal.ofReal (b - a) := Real.volume_Icc
      _ ≤ _ := ENNReal.ofReal_le_ofReal hlen
  have h := hn (Icc a b) hmeasure
  rwa [Measure.restrict_restrict_of_subset hsub] at h

/-- The one-cell endpoint integral discarded when passing from an inclusive
mesh sum to the source's limiting integral is uniformly negligible. -/
theorem eventually_uniform_mesh_cell_integral_abs_lt
    {f : ℝ → ℝ} {K : Set ℝ} (hf : IntegrableOn f K volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ,
      Icc ((b : ℝ) / n) (((b : ℝ) + 1) / n) ⊆ K →
      |∫ t in Icc ((b : ℝ) / n) (((b : ℝ) + 1) / n), f t| < ε := by
  filter_upwards [eventually_uniform_short_interval_integral_abs_lt hf hε] with n hn
  intro b hsub
  exact hn _ _ hsub (by ring_nf; exact le_rfl)

/-- Removing the initial portion of an integrable interval leaves its final
portion. Lebesgue-null endpoints make the closed-interval convention exact. -/
theorem setIntegral_Icc_sub_left {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : IntegrableOn f (Icc a c) volume) :
    (∫ t in Icc a c, f t) - (∫ t in Icc a b, f t) = ∫ t in Icc b c, f t := by
  have hleft : IntegrableOn f (Ioc a b) volume :=
    hf.mono_set (fun _ ht ↦ ⟨ht.1.le, ht.2.trans hbc⟩)
  have hright : IntegrableOn f (Ioc b c) volume :=
    hf.mono_set (fun _ ht ↦ ⟨hab.trans ht.1.le, ht.2⟩)
  have hsum := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl b))
    measurableSet_Ioc hleft hright
  rw [Ioc_union_Ioc_eq_Ioc hab hbc] at hsum
  simp_rw [integral_Icc_eq_integral_Ioc]
  rw [hsum]
  ring

/-- The integral for an inclusive mesh interval differs from the source's
upper-endpoint convention by a uniformly vanishing one-cell contribution. -/
theorem eventually_uniform_mesh_endpoint_difference_abs_lt
    {f : ℝ → ℝ} {K : Set ℝ} (hf : IntegrableOn f K volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ, a ≤ b →
      Icc ((a : ℝ) / n) (((b : ℝ) + 1) / n) ⊆ K →
      |(∫ t in Icc ((a : ℝ) / n) (((b : ℝ) + 1) / n), f t) -
        (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), f t)| < ε := by
  filter_upwards [eventually_uniform_mesh_cell_integral_abs_lt hf hε] with n hn
  intro a b hab hsub
  have hab' : (a : ℝ) / n ≤ (b : ℝ) / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg n)
  have hbc : (b : ℝ) / n ≤ ((b : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by exact le_add_of_nonneg_right zero_le_one)
      (Nat.cast_nonneg n)
  rw [setIntegral_Icc_sub_left hab' hbc (hf.mono_set hsub)]
  apply hn b
  exact fun _ ht ↦ hsub ⟨hab'.trans ht.1, ht.2⟩

end Freezing2
