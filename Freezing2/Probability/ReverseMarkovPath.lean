module

public import Freezing2.Probability.ContinuationConditional
public import Freezing2.Probability.ReverseConditional

/-!
# Exact path probabilities of the reverse history

If every state that is consistent with a prescribed path passes to a
consistent next state with the same deterministic probability, then the
probability that the actual reverse history follows the prescribed path is
the product of these probabilities. The conditional law of the next forest
given the whole past is the actual one-step transition law
(`conditional_endpoint_indicator`), so no independence is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Freezing2.ReverseHistory

open Freezing1

theorem continuation_law_one (x : SignSequence) {s : ℕ} (hs : 0 < s) (F : Reverse.Forest) :
    ReverseContinuation.law x s F 1 = Reverse.transitionLaw x (s - 1) F := by
  simp only [ReverseContinuation.law, hs, ite_true, zero_add]
  exact Measure.dirac_bind measurable_from_top _

theorem jointLaw_eval_zero (x : SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, ω 0 = Reverse.initial x n := by
  have h := traj_map_eval_start x n 0 (initialPrefix x n)
  have hm : (jointLaw x n).map (fun ω : History ↦ ω 0) = Measure.dirac (Reverse.initial x n) := by
    rw [jointLaw, h]
    rfl
  have hae : ∀ᵐ F ∂(jointLaw x n).map (fun ω : History ↦ ω 0), F = Reverse.initial x n := by
    rw [hm]
    exact (ae_dirac_iff (show MeasurableSet {F : Reverse.Forest | F = Reverse.initial x n}
      from trivial)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hae

/-- **Markov step.** If, almost surely on a past event `A`, the next forest falls in
`B` with deterministic one-step probability `q`, then `A` followed by `B` has
probability `P(A) q`. -/
theorem jointLaw_real_inter_succ (x : SignSequence) (n : ℕ) {N : ℕ} (hN : N < n)
    {A : Set History} (hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A)
    (B : Set Reverse.Forest) (q : ℝ)
    (hq : ∀ᵐ ω ∂jointLaw x n, ω ∈ A →
      (Reverse.transitionLaw x (n - (N + 1)) (ω N)).real B = q) :
    (jointLaw x n).real (A ∩ {ω | ω (N + 1) ∈ B}) = (jointLaw x n).real A * q := by
  let μ := jointLaw x n
  have hBm : MeasurableSet {ω : History | ω (N + 1) ∈ B} :=
    (measurable_pi_apply (N + 1)) (show MeasurableSet B from trivial)
  have hc := conditional_endpoint_indicator x (n := n) (a := N) (m := 1) (by omega) B
  have hi : Integrable ({ω : History | ω (N + 1) ∈ B}.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrable_const 1).indicator hBm
  have he := setIntegral_condExp ((Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N) hi hA
  have hcond : ∀ᵐ ω ∂μ, ω ∈ A → (ReverseContinuation.law x (n - N) (ω N) 1).real B = q := by
    filter_upwards [hq] with ω hω hA
    rw [continuation_law_one x (by omega), show n - N - 1 = n - (N + 1) by omega]
    exact hω hA
  have hAmeas : MeasurableSet A := (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N A hA
  have hB_eq : ({ω : History | ω (N + 1) ∈ B}.indicator fun _ ↦ (1 : ℝ)) =
      fun ω : History ↦ B.indicator (fun _ ↦ (1 : ℝ)) (ω (N + 1)) := by
    funext ω
    by_cases h : ω (N + 1) ∈ B <;> simp [h]
  rw [hB_eq] at he hi
  have h1 : ∫ ω in A, (μ[(fun ω : History ↦ B.indicator (fun _ ↦ (1 : ℝ))
      (ω (N + 1))) | Filtration.piLE (X := fun _ ↦ Reverse.Forest) N]) ω ∂μ =
      ∫ ω in A, (ReverseContinuation.law x (n - N) (ω N) 1).real B ∂μ :=
    setIntegral_congr_ae hAmeas (hc.mono fun ω h _ ↦ h)
  have h2 : ∫ ω in A, (ReverseContinuation.law x (n - N) (ω N) 1).real B ∂μ =
      ∫ _ω in A, q ∂μ := setIntegral_congr_ae hAmeas hcond
  have h3 : ∫ ω in A, (fun ω : History ↦ B.indicator (fun _ ↦ (1 : ℝ)) (ω (N + 1))) ω ∂μ =
      μ.real (A ∩ {ω | ω (N + 1) ∈ B}) := by
    rw [← hB_eq, setIntegral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one]
  rw [← h3, ← he, h1, h2, setIntegral_const, smul_eq_mul, mul_comm]

/-- **Markov path product.** Prescribed consistent states `P k` at steps `k`,
with almost-sure side conditions `V k`, and deterministic one-step passage
probabilities `q k` give the exact probability of the whole prescribed path. -/
theorem jointLaw_path_eq_prod (x : SignSequence) (n : ℕ) (P V : ℕ → Set Reverse.Forest)
    (hV : ∀ k ≤ n, ∀ᵐ ω ∂jointLaw x n, ω k ∈ V k) (q : ℕ → ℝ)
    (hq : ∀ k < n, ∀ F ∈ P k ∩ V k,
      (Reverse.transitionLaw x (n - (k + 1)) F).real (P (k + 1)) = q k)
    (h0 : Reverse.initial x n ∈ P 0) :
    ∀ N ≤ n, (jointLaw x n).real {ω | ∀ k ≤ N, ω k ∈ P k} = ∏ k ∈ Finset.range N, q k := by
  intro N
  induction N with
  | zero =>
    intro _
    simp only [nonpos_iff_eq_zero, forall_eq, Finset.range_zero, Finset.prod_empty]
    rw [measureReal_def, measure_congr (show {ω : History | ω 0 ∈ P 0} =ᵐ[jointLaw x n] univ from
      (jointLaw_eval_zero x n).mono fun ω h ↦ by simp [h, h0]), measure_univ,
      ENNReal.toReal_one]
  | succ N ih =>
    intro hN
    let μ := jointLaw x n
    let A : Set History := {ω | ∀ k ≤ N, ω k ∈ P k}
    let B : Set History := {ω | ω (N + 1) ∈ P (N + 1)}
    have hAm : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A := by
      have : A = ⋂ k ∈ Finset.range (N + 1), (fun ω : History ↦ ω k) ⁻¹' P k := by
        ext ω
        simp only [A, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_preimage]
        exact ⟨fun h k hk ↦ h k (by omega), fun h k hk ↦ h k (by omega)⟩
      rw [this]
      exact Finset.measurableSet_biInter _ fun k hk ↦
        (measurable_eval_piLE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
          (show MeasurableSet (P k) from trivial)
    have hBm : MeasurableSet B := (measurable_pi_apply (N + 1)) (show MeasurableSet _ from trivial)
    have hsplit : {ω : History | ∀ k ≤ N + 1, ω k ∈ P k} = A ∩ B := by
      ext ω
      simp only [A, B, mem_ofPred_eq, mem_inter_iff]
      exact ⟨fun h ↦ ⟨fun k hk ↦ h k (by omega), h (N + 1) le_rfl⟩,
        fun h k hk ↦ by
          rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
          · exact h.1 k (by omega)
          · obtain rfl : k = N + 1 := by omega
            exact h.2⟩
    have hc := conditional_endpoint_indicator x (a := N) (m := 1) (by omega) (P (N + 1))
    have hi : Integrable (B.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const 1).indicator hBm
    have he := setIntegral_condExp ((Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N) hi hAm
    have hcond : ∀ᵐ ω ∂μ, ω ∈ A →
        (ReverseContinuation.law x (n - N) (ω N) 1).real (P (N + 1)) = q N := by
      filter_upwards [hV N (by omega)] with ω hω hA
      rw [continuation_law_one x (by omega)]
      rw [show n - N - 1 = n - (N + 1) by omega]
      exact hq N (by omega) (ω N) ⟨hA N le_rfl, hω⟩
    have hAmeas : MeasurableSet A := (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N A hAm
    have hB_eq : (B.indicator fun _ ↦ (1 : ℝ)) =
        fun ω : History ↦ (P (N + 1)).indicator (fun _ ↦ (1 : ℝ)) (ω (N + 1)) := by
      funext ω
      by_cases h : ω (N + 1) ∈ P (N + 1) <;> simp [B, h]
    rw [hB_eq] at he hi
    have h1 : ∫ ω in A, (μ[(fun ω : History ↦ (P (N + 1)).indicator (fun _ ↦ (1 : ℝ))
        (ω (N + 1))) | Filtration.piLE (X := fun _ ↦ Reverse.Forest) N]) ω ∂μ =
        ∫ ω in A, (ReverseContinuation.law x (n - N) (ω N) 1).real (P (N + 1)) ∂μ :=
      setIntegral_congr_ae hAmeas (hc.mono fun ω h _ ↦ h)
    have h2 : ∫ ω in A, (ReverseContinuation.law x (n - N) (ω N) 1).real (P (N + 1)) ∂μ =
        ∫ _ω in A, q N ∂μ := setIntegral_congr_ae hAmeas hcond
    have h3 : ∫ ω in A, (fun ω : History ↦ (P (N + 1)).indicator (fun _ ↦ (1 : ℝ))
        (ω (N + 1))) ω ∂μ = μ.real (A ∩ B) := by
      rw [← hB_eq, setIntegral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one]
    rw [hsplit, ← h3, ← he, h1, h2, setIntegral_const, smul_eq_mul, ih (by omega),
      Finset.prod_range_succ, mul_comm]

end Freezing2.ReverseHistory
