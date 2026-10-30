module

public import Freezing2.Analysis.SublinearPopulation

/-!
# Specialization to the paper's reciprocal notation

The source describes its limiting function as `1/f`. Positivity is required
almost everywhere, allowing the endpoint zeros used in the excursion example.
Keeping that premise explicit prevents the totalized real inverse at zero
from introducing profiles outside the mathematical meaning of the source.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Freezing2

/-- A positive finite source profile has a positive reciprocal almost everywhere.
No condition is imposed on the two endpoint values or any other null set. -/
theorem positiveProfile_reciprocal {f : ℝ → ℝ}
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t) :
    PositiveProfile (fun t ↦ 1 / f t) := by
  exact hf.mono fun _ ht ↦ one_div_pos.mpr ht

/-- Lemma `lem:hnalpha(i)` in the source's `1/f` notation.
The proved general statement does not need the source's local square-moment
condition or its lower bound `0 < α`. -/
theorem population_sublinear_of_sourceProfile {x : ℕ → ℕ → ℤ} {α : ℝ}
    {f : ℝ → ℝ} (hx : AdmissibleArray x) (hα : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
      atTop (𝓝 0) :=
  population_sublinear_at hx hα hL1 (positiveProfile_reciprocal hf) ha0 ha1

/-- Extend the source's positive-horizon array by the canonical all-up row at zero.
Every row used by the source remains exactly the same. -/
def initialRowExtension (x : ℕ → ℕ → ℤ) (n : ℕ) : ℕ → ℤ :=
  if n = 0 then fun _ ↦ 1 else x n

/-- A source array indexed by positive horizons has an admissible extension. -/
theorem admissible_initialRowExtension {x : ℕ → ℕ → ℤ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n) :
    AdmissibleArray (initialRowExtension x) := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · constructor
    · intro i _
      exact Or.inl (by simp [initialRowExtension])
    · intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      simp [hk0, activeCount_zero]
  · simpa only [initialRowExtension, ite_eq_right (Nat.ne_of_gt hn)] using hx n hn

/-- The canonical extension changes only an asymptotically irrelevant row. -/
theorem initialRowExtension_eventually_eq (x : ℕ → ℕ → ℤ) :
    initialRowExtension x =ᶠ[atTop] x := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [initialRowExtension, ite_eq_right (Nat.ne_of_gt hn)]

/-- The source's reciprocal convergence is unchanged by its zero-row convention. -/
theorem hasL1ReciprocalProfile_initialRowExtension {x : ℕ → ℕ → ℤ} {α : ℝ}
    {g : ℝ → ℝ} (hL1 : HasL1ReciprocalProfile x α g) :
    HasL1ReciprocalProfile (initialRowExtension x) α g := by
  refine ⟨hL1.1, hL1.2.congr' ?_⟩
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [reciprocalProfile, hn]

/-- The source-facing version of `hnalpha(i)` needs admissibility only for the
positive horizons actually indexed in the manuscript. -/
theorem population_sublinear_of_positive_horizons {x : ℕ → ℕ → ℤ} {α : ℝ}
    {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : α < 1) (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ ↦ (activeCount (x n) ⌊(n : ℝ) * a⌋₊ : ℝ) / n)
      atTop (𝓝 0) := by
  have h := population_sublinear_of_sourceProfile (admissible_initialRowExtension hx)
    hα hf (hasL1ReciprocalProfile_initialRowExtension hL1) ha0 ha1
  apply h.congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  rw [hn]

end Freezing2
