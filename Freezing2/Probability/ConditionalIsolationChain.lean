module

public import Freezing2.Probability.ConditionalBlockIsolation
public import Freezing2.Probability.FiniteConditionalEventBounds

/-!
# Iterated isolation bounds on the actual reverse history

Successive two-part blocks first allow the younger marked vertices to be born,
then contract their component count. A full-history conditional bound is
iterated through the actual filtration. No independence assertion is needed.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseHistory

open Freezing1 Freezing2.TrackedClusters

theorem oldest_isolation_chain_probability_le {x : SignSequence}
    {n k m : ℕ} {s r K : ℕ → ℕ} {A : ℕ → Finset (ℕ ⊕ ℕ)} {u : ℕ ⊕ ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : 0 < k) (hkn : k ≤ n)
    (hsanti : Antitone s) (hs : ∀ j < m, s j ≤ n)
    (hr : ∀ j < m, r j ≤ s j) (ht : ∀ j < m, s (j + 1) ≤ r j)
    {M : ℝ} (hM : 0 < M) (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (Freezing1.activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hlength : ∀ j < m, tightnessBlockLength M n k ≤ r j - s (j + 1))
    (hA : ∀ j < m, A j ⊆ Freezing1.vertexLabels x n)
    (hcard : ∀ j < m, (A j).card = K j + 1)
    (hK : ∀ j < m, M * Real.sqrt k ≤ K j)
    (hu : ∀ j < m, u ∈ A j) (huBorn : ∀ j < m, s j ≤ Freezing1.birthTime n u)
    (hyoung : ∀ j < m, ∀ v ∈ A j, v ≠ u → Freezing1.birthTime n v ≤ s j)
    (hborn : ∀ j < m, ∀ v ∈ A j, r j ≤ Freezing1.birthTime n v) :
    (jointLaw x n).real (⋂ j ∈ Finset.range m,
      {ω | Alone (ω (n - s (j + 1))) (A j) u}) ≤ (3 / 4 : ℝ) ^ m := by
  let F : Filtration ℕ (inferInstance : MeasurableSpace History) :=
    { seq j := Filtration.piLE (X := fun _ ↦ Forest) (n - s j)
      mono' := by
        intro i j hij
        apply Filtration.piLE.mono
        exact Nat.sub_le_sub_left (hsanti hij) n
      le' j := Filtration.piLE.le (n - s j) }
  let E : ℕ → Set History := fun j ↦ {ω | Alone (ω (n - s (j + 1))) (A j) u}
  apply measureReal_biInter_range_le_pow_of_condExp_indicator F E m
  · intro j _
    exact (show MeasurableSet {G : Forest | Alone G (A j) u} from by trivial).preimage
      (measurable_eval_piLE (le_refl (n - s (j + 1))))
  · norm_num
  · intro j hj
    have hc := conditional_oldest_isolation_le_three_quarters hn hk hkn
      (hs j hj) (hr j hj) (ht j hj) hM hlarge hpop (hlength j hj)
      (hA j hj) (hcard j hj) (hK j hj) (hu j hj) (huBorn j hj)
      (hyoung j hj) (hborn j hj)
    have he : (E j).indicator (fun _ ↦ (1 : ℝ)) =
        fun ω ↦ {G : Forest | Alone G (A j) u}.indicator (fun _ ↦ (1 : ℝ))
          (ω (n - s (j + 1))) := by
      funext ω
      by_cases h : Alone (ω (n - s (j + 1))) (A j) u <;> simp [E, h]
    filter_upwards [hc] with ω hω
    simpa only [he, F] using hω

end Freezing2.ReverseHistory
