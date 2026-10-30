module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Data.Finset.Max

/-!
# Independent events from deterministic conditional probabilities

The reverse height increments have constant conditional probabilities given the
whole past. This module proves, rather than assumes, the independence consequence
needed for their Bernoulli-sum representation.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Freezing2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A constant conditional event probability factors intersections with every
past-measurable event. -/
theorem measureReal_inter_of_condExp_indicator {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {A B : Set Ω} (hA : MeasurableSet[mΩ] A) (hB : MeasurableSet[m] B) {p : ℝ}
    (hc : μ[A.indicator (fun _ ↦ (1 : ℝ)) | m] =ᵐ[μ] fun _ ↦ p) :
    μ.real (B ∩ A) = μ.real B * p := by
  have hi : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have he := setIntegral_condExp hm hi hB
  have hleft : (∫ ω in B, (μ[A.indicator (fun _ ↦ (1 : ℝ)) | m]) ω ∂μ) =
      ∫ _ω in B, p ∂μ := integral_congr_ae (ae_restrict_of_ae hc)
  rw [hleft, setIntegral_indicator hA] at he
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using he.symm

/-- Under deterministic conditional event probabilities, each constant is its
actual unconditional probability. -/
theorem measureReal_of_condExp_indicator {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[mΩ] A) {p : ℝ}
    (hc : μ[A.indicator (fun _ ↦ (1 : ℝ)) | m] =ᵐ[μ] fun _ ↦ p) :
    μ.real A = p := by
  simpa using
    measureReal_inter_of_condExp_indicator (mΩ := mΩ) (μ := μ) hm hA (B := univ) .univ hc

/-- Events revealed one step at a time are independent if their conditional
probabilities given the full preceding filtration are deterministic. -/
theorem iIndepSet_of_condExp_indicator (F : Filtration ℕ mΩ) (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[F (k + 1)] (A k)) (p : ℕ → ℝ)
    (hc : ∀ k, μ[(A k).indicator (fun _ ↦ (1 : ℝ)) | F k] =ᵐ[μ] fun _ ↦ p k) :
    iIndepSet A μ := by
  classical
  have hAm (k : ℕ) : MeasurableSet (A k) := F.le (k + 1) _ (hA k)
  have hp (k : ℕ) : μ.real (A k) = p k :=
    measureReal_of_condExp_indicator (F.le k) (hAm k) (hc k)
  have hprod (s : Finset ℕ) : μ.real (⋂ k ∈ s, A k) = ∏ k ∈ s, μ.real (A k) := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert k s hlt ih =>
      have hnot : k ∉ s := fun hk ↦ (lt_irrefl k) (hlt k hk)
      have hB : MeasurableSet[F k] (⋂ j ∈ s, A j) := by
        apply MeasurableSet.iInter
        intro j
        apply MeasurableSet.iInter
        intro hj
        exact F.mono (Nat.succ_le_of_lt (hlt j hj)) _ (hA j)
      have hf := measureReal_inter_of_condExp_indicator (F.le k) (hAm k) hB (hc k)
      have he : (⋂ j ∈ insert k s, A j) = (⋂ j ∈ s, A j) ∩ A k := by
        ext ω
        simp [and_comm]
      rw [Finset.prod_insert hnot, he, hf, ih, hp]
      ring
  apply (iIndepSet_iff_meas_biInter hAm).mpr
  intro s
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top _ _)).mp
  simpa only [ENNReal.toReal_prod, measureReal_def] using hprod s

end Freezing2
