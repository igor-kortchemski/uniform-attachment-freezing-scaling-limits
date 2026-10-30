module

public import Freezing2.Probability.ReverseHeightLaw
public import Freezing2.Probability.ReverseLabelBridge
public import Freezing2.Probability.HeightApproximation

/-!
# Uniform concentration of the constructed reverse-forest heights

This specializes the concentration engine to the actual joint reverse law.
The Bernoulli laws, independence, means, and family-size bound are all proved.
The maximum includes every legal vertex and every time up to and including
its birth, including time zero. No probabilistic model premise remains.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ProbabilityTheory ENNReal

namespace Freezing2

/-- Exactly the legal vertex/time pairs, with the birth endpoint retained. -/
abbrev ReverseHeightIndex (x : ℕ → ℤ) (n : ℕ) :=
  {p : Fin (n + 1) × {v // v ∈ vertexLabels x n} // p.1.val ≤ birthTime n p.2.val}

theorem card_reverseHeightIndex_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hS : 0 ≤ activeCount x n) : Fintype.card (ReverseHeightIndex x n) ≤ (n + 1) ^ 2 := by
  have hu : (upSteps x 0 n).card ≤ n := by
    simpa only [upSteps, Nat.card_Ioc, Nat.sub_zero] using
      Finset.card_filter_le (Finset.Ioc 0 n) (fun i ↦ x i = 1)
  have hv : (vertexLabels x n).card ≤ n + 1 := by
    rw [vertexLabels_card x hx hS]
    omega
  calc
    _ ≤ Fintype.card (Fin (n + 1) × {v // v ∈ vertexLabels x n}) :=
      Fintype.card_subtype_le _
    _ = (n + 1) * (vertexLabels x n).card := by simp
    _ ≤ _ := by nlinarith

/-- The maximum error between actual heights and the source inclusive harmonic
centres, on the actual reverse-process history. -/
noncomputable def reverseHeightErrorMax (x : ℕ → ℕ → ℤ) (n : ℕ)
    (ω : ReverseHistory.History) : ℝ :=
  finiteHeightDeviationMax
    (fun j : ReverseHeightIndex (x n) n ↦
      ReverseHistory.heightAt n j.val.1.val (toCompanionLabel j.val.2.val))
    (fun j ↦ inclusiveHarmonic (x n) j.val.1.val (birthTime n j.val.2.val) / 2) ω

theorem reverseHeightErrorMax_nonneg (x : ℕ → ℕ → ℤ) (n : ℕ)
    (ω : ReverseHistory.History) : 0 ≤ reverseHeightErrorMax x n ω := by
  unfold reverseHeightErrorMax finiteHeightDeviationMax
  rw [Finset.le_sup'_iff]
  exact ⟨none, Finset.mem_univ _, le_rfl⟩

/-- Every admissible height deviation is bounded by the displayed maximum. -/
theorem height_error_le_reverseHeightErrorMax (x : ℕ → ℕ → ℤ) (n a : ℕ)
    {v : VertexLabel} (hv : v ∈ vertexLabels (x n) n) (ha : a ≤ birthTime n v)
    (ω : ReverseHistory.History) :
    |ReverseHistory.heightAt n a (toCompanionLabel v) ω -
      inclusiveHarmonic (x n) a (birthTime n v) / 2| ≤ reverseHeightErrorMax x n ω := by
  let j : ReverseHeightIndex (x n) n :=
    ⟨(⟨a, by have := birthTime_le (x n) hv; omega⟩, ⟨v, hv⟩), ha⟩
  unfold reverseHeightErrorMax finiteHeightDeviationMax
  rw [Finset.le_sup'_iff]
  exact ⟨some j, Finset.mem_univ _, le_rfl⟩

/-- The maximum has precisely the paper's vertex/time interpretation, including
the extra birth endpoint; no surrogate statistic replaces the actual heights. -/
theorem lt_reverseHeightErrorMax_iff (x : ℕ → ℕ → ℤ) (n : ℕ)
    (ω : ReverseHistory.History) {t : ℝ} (ht : 0 ≤ t) :
    t < reverseHeightErrorMax x n ω ↔
      ∃ v ∈ vertexLabels (x n) n, ∃ a : ℕ, a ≤ birthTime n v ∧
        t < |ReverseHistory.heightAt n a (toCompanionLabel v) ω -
          inclusiveHarmonic (x n) a (birthTime n v) / 2| := by
  rw [reverseHeightErrorMax, lt_finiteHeightDeviationMax_iff _ _ _ ht]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val.2.val, j.val.2.property, j.val.1.val, j.property, hj⟩
  · rintro ⟨v, hv, a, ha, hav⟩
    exact ⟨⟨(⟨a, by have := birthTime_le (x n) hv; omega⟩, ⟨v, hv⟩), ha⟩, hav⟩

/-- Uniform concentration of the actual reverse heights at the source harmonic
centres. The assumptions are the paper's deterministic source hypotheses;
all formerly conditional Bernoulli premises have been discharged. -/
theorem tendsto_reverseHeightErrorMax
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      (ReverseHistory.jointLaw (companionSchedule (x n)) n).real
        {ω | ε * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n ω})
      atTop (𝓝 0) := by
  let a : (n : ℕ) → ReverseHeightIndex (x n) n → ℕ := fun _ j ↦ j.val.1.val
  let v : (n : ℕ) → ReverseHeightIndex (x n) n → ℕ ⊕ ℕ :=
    fun _ j ↦ toCompanionLabel j.val.2.val
  let b : (n : ℕ) → ReverseHeightIndex (x n) n → ℕ :=
    fun n j ↦ Freezing1.birthTime n (v n j)
  let d : (n : ℕ) → ReverseHeightIndex (x n) n → ℕ := fun n j ↦ b n j - a n j
  let Z : (n : ℕ) → ReverseHeightIndex (x n) n → ReverseHistory.History → ℝ :=
    fun n j ↦ ReverseHistory.heightAt n (a n j) (v n j)
  let Y := fun n (j : ReverseHeightIndex (x n) n) ↦
    ReverseHistory.heightBernoulli n (a n j) (v n j)
  let p := fun n (j : ReverseHeightIndex (x n) n) ↦
    ReverseHistory.heightBernoulliParameter (companionSchedule (x n)) n (a n j) (v n j)
  have hn (n : ℕ) : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule (x n)) :=
    (companion_before_extinction (x n) (hx n).1 (hx n).2).le
  have hv (n : ℕ) (j : ReverseHeightIndex (x n) n) :
      v n j ∈ Freezing1.vertexLabels (companionSchedule (x n)) n :=
    toCompanionLabel_mem (x n) (hx n).1 j.val.2.property
  have hab (n : ℕ) (j : ReverseHeightIndex (x n) n) : a n j ≤ b n j := by
    simpa only [a, b, v, companion_birthTime] using j.property
  have hbn (n : ℕ) (j : ReverseHeightIndex (x n) n) : b n j ≤ n :=
    ReverseHistory.birthTime_le_horizon (hv n j)
  have hLaw (n : ℕ) (j : ReverseHeightIndex (x n) n) :
      IdentDistrib (Z n j) (fun ω ↦ ∑ i, Y n j i ω)
        (ReverseHistory.jointLaw (companionSchedule (x n)) n)
        (ReverseHistory.jointLaw (companionSchedule (x n)) n) :=
    ReverseHistory.identDistrib_heightAt_sum_heightBernoulli (hn n) (hv n j) (hab n j)
  have hInd (n : ℕ) (j : ReverseHeightIndex (x n) n) :
      iIndepFun (Y n j) (ReverseHistory.jointLaw (companionSchedule (x n)) n) :=
    ReverseHistory.iIndepFun_heightBernoulli (hn n) (hv n j)
  have hY (n : ℕ) (j : ReverseHeightIndex (x n) n) (i : Fin (d n j)) :
      HasLaw (Y n j i) (bernoulliMeasure (1 : ℝ) 0 (p n j i))
        (ReverseHistory.jointLaw (companionSchedule (x n)) n) :=
    ReverseHistory.hasLaw_heightBernoulli _ _ _ _ _
  have hmean (n : ℕ) (j : ReverseHeightIndex (x n) n) :
      (∑ i, (p n j i : ℝ)) = harmonicUpInterval (x n) (a n j) (b n j - a n j) := by
    simpa only [p, b, harmonicUpInterval, companionSchedule, decide_eq_true_eq,
      companion_activeCount (x n) (hx n).1, one_div] using
      ReverseHistory.sum_heightBernoulliParameter (a := a n j) (hn n) (hv n j)
  have hcard (n : ℕ) : Fintype.card (ReverseHeightIndex (x n) n) ≤ (n + 1) ^ 2 :=
    card_reverseHeightIndex_le (x n) (hx n).1 ((hx n).2 n le_rfl).le
  have h := tendsto_uniform_height_inclusive_harmonic_deviation hx hα0 hα1 hL1 hpos
    (fun n ↦ ReverseHistory.jointLaw (companionSchedule (x n)) n)
    (fun n (_j : ReverseHeightIndex (x n) n) ↦
      ReverseHistory.jointLaw (companionSchedule (x n)) n)
    a b d Z Y p hab hbn hLaw hInd hY hmean hcard hε
  simpa only [reverseHeightErrorMax, a, b, v, Z, companion_birthTime] using h

end Freezing2
