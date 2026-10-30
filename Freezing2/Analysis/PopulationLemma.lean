module

public import Freezing2.Analysis.CoalescenceLimit
public import Freezing2.Analysis.HarmonicConclusions
public import Freezing2.Analysis.SignMeasures
public import Freezing2.Analysis.SourceHypotheses

/-!
# Lemma hnalpha in the source's profile notation

`population_profile_lemma` collects all five conclusions of Lemma
`lem:hnalpha` (source lines 718–750), with the source's limiting profile `f`
and its reciprocal `1/f`. The assumptions contain the global L¹ convergence,
the local second-moment convergence, and the source's standing positivity and
integrability requirements; they contain none of the lemma's conclusions.

The array is extended to horizon zero only for convenient sequence indexing.
`initialRowExtension` is the canonical all-up row at zero and agrees with the
original positive-horizon array eventually. The global L¹ condition and the
local second-moment condition both survive that extension.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Asymptotics

namespace Freezing2

/-- The local square-moment hypothesis does not depend on the unused zero row. -/
theorem hasLocalSquareMomentProfile_initialRowExtension
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (h2 : HasLocalSquareMomentProfile x α g) :
    HasLocalSquareMomentProfile (initialRowExtension x) α g := by
  intro a b ha hab hb
  refine ⟨(h2 a b ha hab hb).1, (h2 a b ha hab hb).2.congr' ?_⟩
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [reciprocalProfile, hn]

/-- The reciprocal-square integral agrees exactly with the paper's integrand.
The algebra is also valid at zeros of `f`, under Lean's total inverse convention. -/
theorem reciprocal_square_half_integral (f : ℝ → ℝ) (s : Set ℝ) :
    (∫ t in s, (1 / f t) ^ 2) / 2 = ∫ t in s, 1 / (2 * (f t) ^ 2) := by
  rw [← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun t ↦ by
    calc
      (1 / f t) ^ 2 / 2 = ((f t) ^ 2)⁻¹ * (2 : ℝ)⁻¹ := by
        rw [one_div, inv_pow, div_eq_mul_inv]
      _ = 1 / (2 * (f t) ^ 2) := by rw [one_div, mul_inv_rev]

/-- The error in part (v) has precisely the limiting integral printed in the source. -/
theorem coalescenceIntervalError_source_formula (x : ℕ → ℕ → ℤ) (α : ℝ)
    (f : ℝ → ℝ) (n a b : ℕ) :
    coalescenceIntervalError x α (fun t ↦ 1 / f t) n a b =
      |((n : ℝ) ^ (2 * α) / n) * coalescenceUpSum (x n) (a - 1) (b + 1 - a) -
        ∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), 1 / (2 * (f t) ^ 2)| := by
  unfold coalescenceIntervalError
  rw [reciprocal_square_half_integral]

/-- Lemma `lem:hnalpha`, all five parts. The two measures in (ii) are exactly
`(2/n) ∑_{i=1}^n 1_{x_i=±1} δ_{i/n}` and converge in the weak topology on finite
measures. Part (iii) uses genuine asymptotic equivalence, not only convergence.
The maxima in (iv) and (v) use inclusive integer intervals and assign zero to
invalid endpoint pairs; this only extends empty-window and zero-horizon cases. -/
theorem population_profile_lemma
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) :
    (∀ a : ℝ, 0 < a → a ≤ 1 →
      Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
        atTop (𝓝 0)) ∧
    (Tendsto (fun n ↦ signTimeMeasure (x n) 1 n) atTop (𝓝 profileFiniteMeasure) ∧
      Tendsto (fun n ↦ signTimeMeasure (x n) (-1) n) atTop (𝓝 profileFiniteMeasure)) ∧
    (((fun n : ℕ ↦ 2 * (n : ℝ) ^ (α - 1) * harmonicUpTotal x n) ~[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n)) ∧
      ((fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n) ~[atTop]
        (fun _ ↦ ∫ t, 1 / f t ∂profileMeasure))) ∧
    (Tendsto (fun n : ℕ ↦ harmonicDeviationMax x n / (n : ℝ) ^ (1 - α))
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (coalescenceIntervalErrorMax x α (fun t ↦ 1 / f t) ε) atTop (𝓝 0)) := by
  have hpos := positiveProfile_reciprocal hf
  refine ⟨?_, ⟨tendsto_upSteps_measure hx hα1 hL1 hpos,
      tendsto_downSteps_measure hx hα1 hL1 hpos⟩,
    ⟨harmonicUpTotal_asymptotic hx hα0 hα1 hL1 hpos,
      harmonicTotal_asymptotic hx hα1 hL1 hpos⟩,
    tendsto_harmonicDeviationMax hx hα0 hα1 hL1 (hpos.mono fun _ ht ↦ ht.le), ?_⟩
  · intro a ha ha1
    exact population_sublinear_of_sourceProfile hx hα1 hf hL1 ha ha1
  · intro ε hε
    exact tendsto_coalescenceIntervalErrorMax hx hα0 hα1 hL1 hpos h2 hε

/-- All five conclusions under exactly the source’s positive-horizon indexing.
The canonical unused row is eliminated from every conclusion. -/
theorem population_profile_lemma_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) :
    (∀ a : ℝ, 0 < a → a ≤ 1 →
      Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
        atTop (𝓝 0)) ∧
    (Tendsto (fun n ↦ signTimeMeasure (x n) 1 n) atTop (𝓝 profileFiniteMeasure) ∧
      Tendsto (fun n ↦ signTimeMeasure (x n) (-1) n) atTop (𝓝 profileFiniteMeasure)) ∧
    (((fun n : ℕ ↦ 2 * (n : ℝ) ^ (α - 1) * harmonicUpTotal x n) ~[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n)) ∧
      ((fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * harmonicTotal x n) ~[atTop]
        (fun _ ↦ ∫ t, 1 / f t ∂profileMeasure))) ∧
    (Tendsto (fun n : ℕ ↦ harmonicDeviationMax x n / (n : ℝ) ^ (1 - α))
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (coalescenceIntervalErrorMax x α (fun t ↦ 1 / f t) ε) atTop (𝓝 0)) := by
  obtain ⟨h1, ⟨hup, hdown⟩, ⟨h3up, h3⟩, h4, h5⟩ :=
    population_profile_lemma (admissible_initialRowExtension hx) hα0 hα1 hf
      (hasL1ReciprocalProfile_initialRowExtension hL1)
      (hasLocalSquareMomentProfile_initialRowExtension h2)
  have htotal : harmonicTotal (initialRowExtension x) =ᶠ[atTop] harmonicTotal x := by
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    simp only [harmonicTotal, hn]
  have huptotal : harmonicUpTotal (initialRowExtension x) =ᶠ[atTop] harmonicUpTotal x := by
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    simp only [harmonicUpTotal, hn]
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha ha1
    apply (h1 a ha ha1).congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    rw [hn]
  · apply hup.congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    rw [hn]
  · apply hdown.congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    rw [hn]
  · apply h3up.congr_left ?_ |>.congr_right ?_
    · filter_upwards [huptotal] with n hn
      rw [hn]
    · filter_upwards [htotal] with n hn
      rw [hn]
  · apply h3.congr_left
    filter_upwards [htotal] with n hn
    rw [hn]
  · apply h4.congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    simp only [harmonicDeviationMax, hn]
  · intro ε hε
    apply (h5 ε hε).congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    simp only [coalescenceIntervalErrorMax, coalescenceIntervalError, hn]

end Freezing2
