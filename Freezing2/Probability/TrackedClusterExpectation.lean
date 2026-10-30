module

public import Freezing2.Probability.TrackedClusterCount
public import Freezing2.Analysis.CoalescentCountRecurrence
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Moments.Variance

/-!
# Expected tracked counts along the actual reverse process

The marginal recursion is obtained by integrating the actual bind transition.
Its quadratic moment inequality is proved from nonnegative variance. A fixed
tracked set is required to have been born at the start of the phase interval;
thereafter every vertex remains present. The final bound counts actual
attachment steps and handles absorption at a single component safely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal BigOperators

namespace Freezing2.TrackedClusters

open Freezing1

/-- Expected number of components after `k` reverse construction steps. -/
noncomputable def expectedCount (x : SignSequence) (n k : ℕ)
    (A : Finset (ℕ ⊕ ℕ)) : ℝ :=
  ∫ F, (componentCount F A : ℝ) ∂Reverse.lawAfter x n k

/-- Every nonempty tracked set has at least one current root, even for the
totalized state space; its count is bounded by its number of vertices. -/
theorem one_le_expectedCount (x : SignSequence) (n k : ℕ)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A.Nonempty) : 1 ≤ expectedCount x n k A := by
  have h := integral_mono (integrable_const (1 : ℝ))
    (integrable_componentCount (Reverse.lawAfter x n k) A) (fun F ↦
      show (1 : ℝ) ≤ componentCount F A by exact_mod_cast componentCount_pos F hA)
  simpa only [integral_const, probReal_univ, one_smul, expectedCount] using h

theorem expectedCount_le_card (x : SignSequence) (n k : ℕ) (A : Finset (ℕ ⊕ ℕ)) :
    expectedCount x n k A ≤ A.card := by
  have h := integral_mono (integrable_componentCount (Reverse.lawAfter x n k) A)
    (integrable_const (A.card : ℝ)) (fun F ↦
      show (componentCount F A : ℝ) ≤ A.card by exact_mod_cast componentCount_le_card F A)
  simpa only [integral_const, probReal_univ, one_smul, expectedCount] using h

variable {V : Type*} [DecidableEq V]

/-- The squared count is bounded, hence integrable under every finite forest law. -/
theorem integrable_componentCount_sq (μ : Measure (RootedForest V)) [IsFiniteMeasure μ]
    (A : Finset V) : Integrable (fun F ↦ (componentCount F A : ℝ) ^ 2) μ := by
  apply Integrable.mono' (integrable_const ((A.card : ℝ) ^ 2))
    measurable_from_top.aestronglyMeasurable
  exact Eventually.of_forall fun F ↦ by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hc : (componentCount F A : ℝ) ≤ A.card := by exact_mod_cast componentCount_le_card F A
    have h0 : (0 : ℝ) ≤ componentCount F A := by positivity
    have hN0 : (0 : ℝ) ≤ A.card := by positivity
    nlinarith

theorem integrable_componentCount_factorial (μ : Measure (RootedForest V))
    [IsFiniteMeasure μ] (A : Finset V) :
    Integrable (fun F ↦ (componentCount F A : ℝ) * ((componentCount F A : ℝ) - 1)) μ := by
  convert (integrable_componentCount_sq μ A).sub (integrable_componentCount μ A) using 1
  ext F
  simp only [Pi.sub_apply]
  ring

/-- Jensen's quadratic bound, proved from variance rather than assumed for
the forest process. -/
theorem expected_factorialCount_ge (μ : Measure (RootedForest V)) [IsProbabilityMeasure μ]
    (A : Finset V) :
    (∫ F, (componentCount F A : ℝ) ∂μ) * ((∫ F, (componentCount F A : ℝ) ∂μ) - 1) ≤
      ∫ F, (componentCount F A : ℝ) * ((componentCount F A : ℝ) - 1) ∂μ := by
  have hmem : MemLp (fun F ↦ (componentCount F A : ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_from_top.aestronglyMeasurable).mpr
      (integrable_componentCount_sq μ A)
  have hv := variance_nonneg (fun F ↦ (componentCount F A : ℝ)) μ
  rw [variance_eq_sub hmem] at hv
  simp only [Pi.pow_apply] at hv
  have he : (∫ F, (componentCount F A : ℝ) * ((componentCount F A : ℝ) - 1) ∂μ) =
      (∫ F, (componentCount F A : ℝ) ^ 2 ∂μ) - ∫ F, (componentCount F A : ℝ) ∂μ := by
    rw [← integral_sub (integrable_componentCount_sq μ A) (integrable_componentCount μ A)]
    congr 1
    ext F
    ring
  rw [he]
  nlinarith [hv]

/-- Integrating a transition against the current law is the actual bind rule.
The kernel integral theorem supplies this identity for the bounded count. -/
theorem integral_bind_componentCount (x : SignSequence) (i : ℕ)
    (μ : Measure Reverse.Forest) [IsProbabilityMeasure μ] (A : Finset (ℕ ⊕ ℕ)) :
    (∫ G, (componentCount G A : ℝ) ∂μ.bind (Reverse.transitionLaw x i)) =
      ∫ F, ∫ G, (componentCount G A : ℝ) ∂Reverse.transitionLaw x i F ∂μ := by
  let κ : Kernel Reverse.Forest Reverse.Forest := ⟨Reverse.transitionLaw x i, measurable_from_top⟩
  have : IsProbabilityMeasure (μ.bind (Reverse.transitionLaw x i)) :=
    isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Eventually.of_forall fun F ↦ Reverse.transitionLaw_probability x i F)
  have hi := integrable_componentCount (μ.bind (Reverse.transitionLaw x i)) A
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (η := κ) (a := ())
    (f := fun G ↦ (componentCount G A : ℝ)) (by
      simpa only [Kernel.comp_apply, Kernel.const_apply, κ, Kernel.coe_mk] using hi)
  simpa only [Kernel.comp_apply, Kernel.const_apply, κ, Kernel.coe_mk] using h

/-- Legal tracked vertices born by the stated source phase are present in
almost every current forest. -/
theorem lawAfter_tracked_present (x : SignSequence) {n k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ vertexLabels x n)
    (hborn : ∀ v ∈ A, n - k ≤ birthTime n v) :
    ∀ᵐ F ∂Reverse.lawAfter x n k, A ⊆ F.vertices := by
  filter_upwards [Reverse.lawAfter_valid x n k hn hk] with F hF
  intro v hv
  rw [hF.vertices_eq]
  exact (Reverse.mem_phaseLabels_iff_birthTime (Nat.sub_le _ _) (hA hv)).mpr (hborn v hv)

/-- The exact marginal expectation recursion, with the factorial second
moment obtained from the genuine transition kernel. -/
theorem expectedCount_succ_eq {x : SignSequence} {n k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ vertexLabels x n)
    (hborn : ∀ v ∈ A, n - k ≤ birthTime n v) :
    expectedCount x n (k + 1) A = expectedCount x n k A -
      if x (n - k) then
        (∫ F, (componentCount F A : ℝ) * ((componentCount F A : ℝ) - 1)
          ∂Reverse.lawAfter x n k) /
            ((activeCount x (n - k) : ℝ) * ((activeCount x (n - k) : ℝ) - 1))
      else 0 := by
  have ht : n - (k + 1) + 1 = n - k := by omega
  have htτ : ((n - k : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast Nat.sub_le n k) hn
  have hS : ((activeCount x (n - k)).toNat : ℝ) = (activeCount x (n - k) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime htτ)
  unfold expectedCount
  rw [Reverse.lawAfter, ite_eq_left hk, integral_bind_componentCount]
  have heq := integral_congr_ae (show
      (fun F ↦ ∫ G, (componentCount G A : ℝ) ∂Reverse.transitionLaw x (n - (k + 1)) F)
        =ᵐ[Reverse.lawAfter x n k]
      fun F ↦ (componentCount F A : ℝ) - if x (n - k) then
        (componentCount F A : ℝ) * ((componentCount F A : ℝ) - 1) /
          ((activeCount x (n - k) : ℝ) * ((activeCount x (n - k) : ℝ) - 1))
      else 0 from by
    filter_upwards [Reverse.lawAfter_valid x n k hn hk.le,
      lawAfter_tracked_present x hn hk.le hA hborn] with F hF hpresent
    have hF' : Reverse.ValidAt x n (n - (k + 1) + 1) F := by simpa only [ht] using hF
    rw [integral_transitionLaw_componentCount hn (by omega) hF' hpresent, ht]
    cases hsgn : x (n - k)
    · rfl
    · simp only [↓reduceIte, Nat.cast_choose_two, hS]
      congr 1
      exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _)
  rw [heq]
  cases hsgn : x (n - k)
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
  · simp only [↓reduceIte]
    rw [integral_sub (integrable_componentCount _ A)
      ((integrable_componentCount_factorial _ A).div_const _), integral_div]

/-- The actual expectation satisfies the source quadratic decrement whenever
the population square is bounded. The moment inequality is proved above. -/
theorem expectedCount_succ_le {x : SignSequence} {n k : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, n - k ≤ birthTime n v) {B : ℝ}
    (hpop : x (n - k) = true → (activeCount x (n - k) : ℝ) ^ 2 ≤ B) :
    expectedCount x n (k + 1) A ≤ expectedCount x n k A -
      (if x (n - k) then 1 else 0) * expectedCount x n k A *
        (expectedCount x n k A - 1) / B := by
  rw [expectedCount_succ_eq hn hk hA hborn]
  cases hsgn : x (n - k)
  · simp
  · simp only [↓reduceIte, one_mul]
    have hu := one_le_expectedCount x n k hA0
    have hprod : 0 ≤ expectedCount x n k A * (expectedCount x n k A - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have ht : n - (k + 1) + 1 = n - k := by omega
    have htτ : ((n - (k + 1) + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast (show n - (k + 1) + 1 ≤ n by omega)) hn
    have htwoN := two_le_activeCount_toNat_succ_of_attachment htτ (by simpa only [ht] using hsgn)
    rw [ht] at htwoN
    have hS : ((activeCount x (n - k)).toNat : ℝ) = (activeCount x (n - k) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg
        (activeCount_nonneg_of_le_extinctionTime (le_trans (by exact_mod_cast Nat.sub_le n k) hn))
    have htwo : (2 : ℝ) ≤ activeCount x (n - k) := by
      rw [← hS]
      exact_mod_cast htwoN
    have hden : 0 < (activeCount x (n - k) : ℝ) * ((activeCount x (n - k) : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have hdenB : (activeCount x (n - k) : ℝ) * ((activeCount x (n - k) : ℝ) - 1) ≤ B := by
      have hp := hpop hsgn
      nlinarith
    have hj := expected_factorialCount_ge (Reverse.lawAfter x n k) A
    change expectedCount x n k A * (expectedCount x n k A - 1) ≤ _ at hj
    apply sub_le_sub_left
    exact (div_le_div_of_nonneg_left hprod hden hdenB).trans
      (div_le_div_of_nonneg_right hj hden.le)

/-- The exact source-sign count over an elapsed reverse-time block. -/
def attachmentSteps (x : SignSequence) (n k₀ m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun j ↦ x (n - (k₀ + j)))

theorem sum_attachment_indicators (x : SignSequence) (n k₀ m : ℕ) :
    (∑ j ∈ Finset.range m, if x (n - (k₀ + j)) then (1 : ℝ) else 0) =
      (attachmentSteps x n k₀ m).card := by
  simp only [attachmentSteps, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- A bound for the actual expected component count over a specified phase
interval, not for an abstract sequence postulated to obey a recurrence.
All tracked vertices are born at its initial phase, and the denominator is
the positive number of actual attachment steps in the interval. -/
theorem expectedCount_block_bound {x : SignSequence} {n k₀ m : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hblock : k₀ + m ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ vertexLabels x n) (hA0 : A.Nonempty)
    (hborn : ∀ v ∈ A, n - k₀ ≤ birthTime n v) {B : ℝ} (hB : 0 < B)
    (hpop : ∀ j < m, x (n - (k₀ + j)) = true →
      (activeCount x (n - (k₀ + j)) : ℝ) ^ 2 ≤ B)
    (hup : 0 < (attachmentSteps x n k₀ m).card) :
    expectedCount x n (k₀ + m) A ≤ 1 + B / (attachmentSteps x n k₀ m).card := by
  have hsum : 0 < ∑ j ∈ Finset.range m,
      if x (n - (k₀ + j)) then (1 : ℝ) else 0 := by
    rw [sum_attachment_indicators]
    exact_mod_cast hup
  have h := expected_cluster_count_bound_of_recurrence
    (fun j ↦ expectedCount x n (k₀ + j) A)
    (fun j ↦ if x (n - (k₀ + j)) then (1 : ℝ) else 0) hB
    (fun j _ ↦ one_le_expectedCount x n (k₀ + j) hA0)
    (fun j _ ↦ by split_ifs <;> norm_num) (fun j hj ↦ ?_) hsum
  · simpa only [sum_attachment_indicators] using h
  · have hborn' : ∀ v ∈ A, n - (k₀ + j) ≤ birthTime n v := by
      intro v hv
      exact le_trans (Nat.sub_le_sub_left (Nat.le_add_right k₀ j) n) (hborn v hv)
    simpa only [Nat.add_assoc] using expectedCount_succ_le hn (by omega) hA hA0
      hborn' (hpop j hj)

end Freezing2.TrackedClusters
