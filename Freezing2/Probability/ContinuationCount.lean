module

public import Freezing2.Probability.ReverseContinuation
public import Freezing2.Probability.TrackedClusterBlock

/-!
# Expected marked counts after an arbitrary valid initial forest

The actual kernel recurrence and variance argument hold uniformly in the
starting forest. This is the count ingredient for conditional block bounds;
no independence between different blocks is asserted.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace Freezing2.ReverseContinuation

open Freezing1 Freezing2.TrackedClusters

noncomputable def expectedCountFrom (x : SignSequence) (s : ℕ) (F : Reverse.Forest)
    (j : ℕ) (A : Finset (ℕ ⊕ ℕ)) : ℝ :=
  ∫ G, (componentCount G A : ℝ) ∂law x s F j

theorem one_le_expectedCountFrom (x : SignSequence) (s : ℕ) (F : Reverse.Forest)
    (j : ℕ) {A : Finset (ℕ ⊕ ℕ)} (hA : A.Nonempty) :
    1 ≤ expectedCountFrom x s F j A := by
  have h := integral_mono (integrable_const (1 : ℝ))
    (integrable_componentCount (law x s F j) A) (fun G ↦
      show (1 : ℝ) ≤ componentCount G A by exact_mod_cast componentCount_pos G hA)
  simpa only [integral_const, probReal_univ, one_smul, expectedCountFrom] using h

/-- Exact recurrence for the actual continuation, with no equation assumed
for its expectation or for a putative partition-valued process. -/
theorem expectedCountFrom_succ_eq {x : SignSequence} {n s j : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n)
    (hF : Reverse.ValidAt x n s F) (hj : j < s)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    (hborn : ∀ v ∈ A, s - j ≤ Freezing1.birthTime n v) :
    expectedCountFrom x s F (j + 1) A = expectedCountFrom x s F j A -
      if x (s - j) then
        (∫ G, (componentCount G A : ℝ) * ((componentCount G A : ℝ) - 1)
          ∂law x s F j) /
          ((Freezing1.activeCount x (s - j) : ℝ) * ((Freezing1.activeCount x (s - j) : ℝ) - 1))
      else 0 := by
  have ht : s - (j + 1) + 1 = s - j := by omega
  have htτ : ((s - j : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast (Nat.sub_le s j).trans hs) hn
  have hS : ((Freezing1.activeCount x (s - j)).toNat : ℝ) =
      (Freezing1.activeCount x (s - j) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime htτ)
  unfold expectedCountFrom
  rw [law, ite_eq_left hj, integral_bind_componentCount]
  have heq := integral_congr_ae (show
      (fun G ↦ ∫ H, (componentCount H A : ℝ) ∂Reverse.transitionLaw x (s - (j + 1)) G)
        =ᵐ[law x s F j]
      fun G ↦ (componentCount G A : ℝ) - if x (s - j) then
        (componentCount G A : ℝ) * ((componentCount G A : ℝ) - 1) /
          ((Freezing1.activeCount x (s - j) : ℝ) * ((Freezing1.activeCount x (s - j) : ℝ) - 1))
      else 0 from by
    filter_upwards [law_valid hn hs hj.le hF,
      law_tracked_present hn hs hj.le hF hA hborn] with G hG hpresent
    have hG' : Reverse.ValidAt x n (s - (j + 1) + 1) G := by simpa only [ht] using hG
    rw [integral_transitionLaw_componentCount hn (by omega) hG' hpresent, ht]
    cases hsgn : x (s - j)
    · rfl
    · simp only [↓reduceIte, Nat.cast_choose_two, hS]
      congr 1
      exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _)
  rw [heq]
  cases hsgn : x (s - j)
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
  · simp only [↓reduceIte]
    rw [integral_sub (integrable_componentCount _ A)
      ((integrable_componentCount_factorial _ A).div_const _), integral_div]

theorem expectedCountFrom_succ_le {x : SignSequence} {n s j : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n)
    (hF : Reverse.ValidAt x n s F) (hj : j < s)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, s - j ≤ Freezing1.birthTime n v) {B : ℝ}
    (hpop : x (s - j) = true → (Freezing1.activeCount x (s - j) : ℝ) ^ 2 ≤ B) :
    expectedCountFrom x s F (j + 1) A ≤ expectedCountFrom x s F j A -
      (if x (s - j) then 1 else 0) * expectedCountFrom x s F j A *
        (expectedCountFrom x s F j A - 1) / B := by
  rw [expectedCountFrom_succ_eq hn hs hF hj hA hborn]
  cases hsgn : x (s - j)
  · simp
  · simp only [↓reduceIte, one_mul]
    have hu := one_le_expectedCountFrom x s F j hA0
    have hprod : 0 ≤ expectedCountFrom x s F j A * (expectedCountFrom x s F j A - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have ht : s - (j + 1) + 1 = s - j := by omega
    have htτ : ((s - (j + 1) + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast (show s - (j + 1) + 1 ≤ n by omega)) hn
    have htwoN := two_le_activeCount_toNat_succ_of_attachment htτ (by simpa only [ht] using hsgn)
    rw [ht] at htwoN
    have hS : ((Freezing1.activeCount x (s - j)).toNat : ℝ) =
        (Freezing1.activeCount x (s - j) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg
        (activeCount_nonneg_of_le_extinctionTime
          (le_trans (by exact_mod_cast (Nat.sub_le s j).trans hs) hn))
    have htwo : (2 : ℝ) ≤ Freezing1.activeCount x (s - j) := by
      rw [← hS]
      exact_mod_cast htwoN
    have hden : 0 < (Freezing1.activeCount x (s - j) : ℝ) *
        ((Freezing1.activeCount x (s - j) : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    have hdenB : (Freezing1.activeCount x (s - j) : ℝ) *
        ((Freezing1.activeCount x (s - j) : ℝ) - 1) ≤ B := by
      have hp := hpop hsgn
      nlinarith
    have hv := expected_factorialCount_ge (law x s F j) A
    change expectedCountFrom x s F j A * (expectedCountFrom x s F j A - 1) ≤ _ at hv
    apply sub_le_sub_left
    exact (div_le_div_of_nonneg_left hprod hden hdenB).trans
      (div_le_div_of_nonneg_right hv hden.le)

/-- Uniform expected-count bound for any valid starting forest, over the
actual positive number of attachment steps. -/
theorem expectedCountFrom_block_bound {x : SignSequence} {n s j₀ m : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hm : j₀ + m ≤ s)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, s - j₀ ≤ Freezing1.birthTime n v) {B : ℝ} (hB : 0 < B)
    (hpop : ∀ j < m, x (s - (j₀ + j)) = true →
      (Freezing1.activeCount x (s - (j₀ + j)) : ℝ) ^ 2 ≤ B)
    (hup : 0 < (attachmentSteps x s j₀ m).card) :
    expectedCountFrom x s F (j₀ + m) A ≤ 1 + B / (attachmentSteps x s j₀ m).card := by
  have hsum : 0 < ∑ j ∈ Finset.range m, if x (s - (j₀ + j)) then (1 : ℝ) else 0 := by
    simpa only [← sum_attachment_indicators, Nat.zero_add] using
      (show (0 : ℝ) < (attachmentSteps x s j₀ m).card by exact_mod_cast hup)
  have h := expected_cluster_count_bound_of_recurrence (fun j ↦ expectedCountFrom x s F (j₀ + j) A)
    (fun j ↦ if x (s - (j₀ + j)) then (1 : ℝ) else 0) hB
    (fun j _ ↦ one_le_expectedCountFrom x s F (j₀ + j) hA0)
    (fun j _ ↦ by split_ifs <;> norm_num)
    (fun j hj ↦ expectedCountFrom_succ_le hn hs hF (by omega) hA hA0
      (fun v hv ↦ (show s - (j₀ + j) ≤ s - j₀ by omega).trans (hborn v hv)) (hpop j hj)) hsum
  simpa only [← sum_attachment_indicators, Nat.zero_add] using h

/-- The population-capped block estimate is uniform over the valid initial
forest. It can therefore be used after conditioning once the actual continuation
identity has been established. -/
theorem expectedCountFrom_block_bound_of_population_bound
    {x : SignSequence} {n s j₀ m : ℕ} {F : Reverse.Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hs : s ≤ n) (hm : j₀ + m ≤ s)
    (hF : Reverse.ValidAt x n s F) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, s - j₀ ≤ Freezing1.birthTime n v)
    {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ t ≤ n, (Freezing1.activeCount x t : ℝ) ≤ M) (hmM : M < m) :
    expectedCountFrom x s F (j₀ + m) A ≤ 1 + 2 * M ^ 2 / ((m : ℝ) - M) := by
  have hsτ : (s : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast hs) hn
  have hcount := attachmentSteps_card_lower_bound hsτ
    hm (fun t ht ↦ hM t (ht.trans hs))
  have hden : 0 < ((m : ℝ) - M) / 2 := by linarith
  have hpos : 0 < (attachmentSteps x s j₀ m).card := by
    exact_mod_cast hden.trans_le hcount
  have hp : ∀ j < m, x (s - (j₀ + j)) = true →
      (Freezing1.activeCount x (s - (j₀ + j)) : ℝ) ^ 2 ≤ M ^ 2 := by
    intro j _ _
    have htτ : ((s - (j₀ + j) : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast (Nat.sub_le s (j₀ + j)).trans hs) hn
    have h0 : (0 : ℝ) ≤ Freezing1.activeCount x (s - (j₀ + j)) := by
      exact_mod_cast activeCount_nonneg_of_le_extinctionTime htτ
    have hu := hM (s - (j₀ + j)) ((Nat.sub_le s (j₀ + j)).trans hs)
    nlinarith
  apply (expectedCountFrom_block_bound hn hs hm hF hA hA0 hborn
    (sq_pos_of_pos hM0) hp hpos).trans
  apply add_le_add le_rfl
  calc
    M ^ 2 / (attachmentSteps x s j₀ m).card ≤ M ^ 2 / (((m : ℝ) - M) / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg M) hden hcount
    _ = _ := by rw [div_div_eq_mul_div]; ring

end Freezing2.ReverseContinuation
