module

public import Freezing2.Probability.ConditionalBernoulli

/-!
# Iterating conditional probability bounds

A uniform upper bound given the full past yields a product upper bound for
successive events. It does not imply their independence. This is the tower
argument used in place of the independence assertion in source U37.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Freezing2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measureReal_inter_le_of_condExp_indicator {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {A B : Set Ω} (hA : MeasurableSet[mΩ] A) (hB : MeasurableSet[m] B) {p : ℝ}
    (hc : μ[A.indicator (fun _ ↦ (1 : ℝ)) | m] ≤ᵐ[μ] fun _ ↦ p) :
    μ.real (B ∩ A) ≤ μ.real B * p := by
  have hi : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have he := setIntegral_condExp hm hi hB
  have hle : (∫ ω in B, (μ[A.indicator (fun _ ↦ (1 : ℝ)) | m]) ω ∂μ) ≤
      ∫ _ω in B, p ∂μ :=
    integral_mono_ae integrable_condExp.integrableOn (integrable_const p)
      (ae_restrict_of_ae hc)
  rw [he, setIntegral_indicator hA] at hle
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using hle

/-- The product bound also retains an arbitrary event already known at the
initial time, which is useful when conditioning on the sampled marks. -/
theorem measureReal_past_inter_biInter_le_prod (F : Filtration ℕ mΩ) (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[F (k + 1)] (A k)) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hc : ∀ k, μ[(A k).indicator (fun _ ↦ (1 : ℝ)) | F k] ≤ᵐ[μ] fun _ ↦ p k)
    {B : Set Ω} (hB : MeasurableSet[F 0] B) (s : Finset ℕ) :
    μ.real (B ∩ ⋂ k ∈ s, A k) ≤ μ.real B * ∏ k ∈ s, p k := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert k s hlt ih =>
      have hnot : k ∉ s := fun hk ↦ (lt_irrefl k) (hlt k hk)
      have hpast : MeasurableSet[F k] (B ∩ ⋂ j ∈ s, A j) := by
        apply (F.mono (Nat.zero_le k) _ hB).inter
        apply MeasurableSet.iInter
        intro j
        apply MeasurableSet.iInter
        intro hj
        exact F.mono (Nat.succ_le_of_lt (hlt j hj)) _ (hA j)
      have hle := measureReal_inter_le_of_condExp_indicator (F.le k)
        (F.le (k + 1) _ (hA k)) hpast (hc k)
      have he : (B ∩ ⋂ j ∈ insert k s, A j) = (B ∩ ⋂ j ∈ s, A j) ∩ A k := by
        ext ω
        simp only [mem_inter_iff, mem_iInter, Finset.mem_insert]
        aesop
      rw [he, Finset.prod_insert hnot]
      calc
        _ ≤ μ.real (B ∩ ⋂ j ∈ s, A j) * p k := hle
        _ ≤ (μ.real B * ∏ j ∈ s, p j) * p k := mul_le_mul_of_nonneg_right ih (hp k)
        _ = _ := by ring

theorem measureReal_biInter_le_prod_of_condExp_indicator (F : Filtration ℕ mΩ)
    (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet[F (k + 1)] (A k))
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hc : ∀ k, μ[(A k).indicator (fun _ ↦ (1 : ℝ)) | F k] ≤ᵐ[μ] fun _ ↦ p k)
    (s : Finset ℕ) :
    μ.real (⋂ k ∈ s, A k) ≤ ∏ k ∈ s, p k := by
  simpa using measureReal_past_inter_biInter_le_prod F A hA p hp hc (B := univ) .univ s

end Freezing2
