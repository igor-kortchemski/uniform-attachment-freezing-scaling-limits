module

public import Freezing2.Probability.ConditionalEventBounds

/-!
# Conditional product bounds for a finite time interval

Only the finitely many event bounds being multiplied are required.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators

namespace Freezing2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measureReal_biInter_range_le_pow_of_condExp_indicator
    (F : Filtration ℕ mΩ) (A : ℕ → Set Ω) (m : ℕ)
    (hA : ∀ j < m, MeasurableSet[F (j + 1)] (A j)) {q : ℝ} (hq : 0 ≤ q)
    (hc : ∀ j < m, μ[(A j).indicator (fun _ ↦ (1 : ℝ)) | F j] ≤ᵐ[μ] fun _ ↦ q) :
    μ.real (⋂ j ∈ Finset.range m, A j) ≤ q ^ m := by
  let A' : ℕ → Set Ω := fun j ↦ if j < m then A j else ∅
  have hA' (j : ℕ) : MeasurableSet[F (j + 1)] (A' j) := by
    dsimp [A']
    split_ifs with hj
    · exact hA j hj
    · exact @MeasurableSet.empty Ω (F (j + 1))
  have hc' (j : ℕ) : μ[(A' j).indicator (fun _ ↦ (1 : ℝ)) | F j] ≤ᵐ[μ] fun _ ↦ q := by
    dsimp [A']
    split_ifs with hj
    · exact hc j hj
    · simp only [Set.indicator_empty]
      change μ[(0 : Ω → ℝ) | F j] ≤ᵐ[μ] fun _ ↦ q
      rw [condExp_zero]
      exact Eventually.of_forall fun _ ↦ hq
  have h := measureReal_biInter_le_prod_of_condExp_indicator F A' hA'
    (fun _ ↦ q) (fun _ ↦ hq) hc' (Finset.range m)
  have he : (⋂ j ∈ Finset.range m, A' j) = ⋂ j ∈ Finset.range m, A j := by
    ext ω
    simp only [mem_iInter, Finset.mem_range]
    constructor <;> intro hω j hj <;> simpa only [A', ite_eq_left hj] using hω j hj
  simpa only [he, Finset.prod_const, Finset.card_range] using h

end Freezing2
