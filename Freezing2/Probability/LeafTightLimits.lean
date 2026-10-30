module

public import Freezing2.Probability.LeafTightTightness

/-!
# Subsequential limits in the leaf-tightness criterion

Every subsequential weak limit `Q` of the laws in Proposition `C.1` has the
prescribed annealed sampled matrices, because the annealed laws depend
continuously on the law of the space. Its annealed covering-radius tails
vanish, by the Portmanteau bound on open sets, and Markov's inequality then
shows that `Q`-almost every space has full support: a space without full
support has covering-radius tail exactly one at some fixed scale for every
sample size. No monotonicity in the sample size is needed.

Given uniqueness of laws with equal annealed matrices among almost surely
fully supported laws, the criterion follows from Prokhorov's theorem.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

universe u

namespace Freezing2.MeasuredGHSpace

/-- If at every scale `1/(m+1)` some covering-radius tail is below one, the
measure has full support. -/
theorem hasFullSupport_of_forall_exists_lt_one (X : MeasuredGHSpace.{u})
    (h : ∀ m : ℕ, ∃ k, (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi (1 / ((m : ℝ) + 1))) < 1) :
    HasFullSupport X := by
  induction X using Quotient.inductionOn with
  | _ X =>
    change Measure.IsOpenPosMeasure (X.law : Measure X)
    by_contra hnot
    obtain ⟨ε, hε, htail⟩ :=
      exists_coverRadius_tail_eq_one_of_not_fullSupport X hnot
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := h m
    have hmono : (iidCoverRadiusLaw X k : Measure ℝ) (Ioi ε) ≤
        (iidCoverRadiusLaw X k : Measure ℝ) (Ioi (1 / ((m : ℝ) + 1))) :=
      measure_mono (Ioi_subset_Ioi hm.le)
    rw [htail k] at hmono
    exact (not_lt_of_ge hmono) hk

/-- Vanishing annealed covering-radius tails give full support almost surely. -/
theorem ae_hasFullSupport_of_tendsto (Q : ProbabilityMeasure MeasuredGHSpace.{u})
    (h : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun k ↦ (annealedCoverRadiusLaw Q k : Measure ℝ) (Ioi δ)) atTop (𝓝 0)) :
    ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X := by
  let A : ℕ → Set MeasuredGHSpace.{u} := fun m ↦
    {X | ∀ k, 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi (1 / ((m : ℝ) + 1)))}
  have hnull (m : ℕ) : (Q : Measure MeasuredGHSpace.{u}) (A m) = 0 := by
    have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' (h _ hδ)
    intro k
    rw [annealedCoverRadiusLaw, continuousMixture_apply _ _ measurableSet_Ioi]
    calc
      (Q : Measure MeasuredGHSpace.{u}) (A m) ≤ (Q : Measure MeasuredGHSpace.{u})
          {X | 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi (1 / ((m : ℝ) + 1)))} :=
        measure_mono fun X hX ↦ hX k
      _ = 1 * (Q : Measure MeasuredGHSpace.{u})
          {X | 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi (1 / ((m : ℝ) + 1)))} :=
        (one_mul _).symm
      _ ≤ _ := mul_meas_ge_le_lintegral₀
        (measurable_sampledCoverRadiusLaw_apply k measurableSet_Ioi).aemeasurable 1
  rw [ae_iff]
  apply measure_mono_null _ (measure_iUnion_null hnull)
  intro X hX
  simp only [mem_ofPred_eq] at hX
  by_contra hcon
  simp only [mem_iUnion, A, mem_ofPred_eq, not_exists, not_forall, not_le] at hcon
  exact hX (hasFullSupport_of_forall_exists_lt_one X hcon)

variable {P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}}
  {L : ∀ k : ℕ, ProbabilityMeasure (Fin k → Fin k → ℝ)}

/-- A subsequential limit has the prescribed annealed sampled matrices. -/
theorem annealedDistanceLaw_eq_of_tendsto_comp
    (hM : ∀ k : ℕ, Tendsto (fun n ↦ annealedDistanceLaw (P n) k) atTop
      (𝓝 (L k)))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Q : ProbabilityMeasure MeasuredGHSpace.{u}}
    (hQ : Tendsto (P ∘ φ) atTop (𝓝 Q)) (k : ℕ) :
    annealedDistanceLaw Q k = L k :=
  tendsto_nhds_unique (tendsto_continuousMixture hQ (continuous_sampledDistanceLaw k))
    ((hM k).comp hφ)

/-- A subsequential limit inherits vanishing annealed covering-radius tails. -/
theorem tendsto_annealedCoverRadius_of_tendsto_comp
    (hleaf : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Q : ProbabilityMeasure MeasuredGHSpace.{u}}
    (hQ : Tendsto (P ∘ φ) atTop (𝓝 Q)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k ↦ (annealedCoverRadiusLaw Q k : Measure ℝ) (Ioi δ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hleaf δ hδ)
    (fun _ ↦ bot_le)
  intro k
  have hconv := tendsto_continuousMixture hQ (continuous_sampledCoverRadiusLaw k)
  calc
    (annealedCoverRadiusLaw Q k : Measure ℝ) (Ioi δ) ≤ liminf (fun i ↦
        (annealedCoverRadiusLaw (P (φ i)) k : Measure ℝ) (Ioi δ)) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv isOpen_Ioi
    _ ≤ limsup (fun i ↦ (annealedCoverRadiusLaw (P (φ i)) k : Measure ℝ) (Ioi δ)) atTop :=
      liminf_le_limsup
    _ ≤ limsup (fun n ↦ (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop :=
      hφ.limsup_comp_le_limsup (u := fun n ↦ (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ))

/-- **Proposition `C.1` for a family of block laws, assuming identification of laws.**
If two laws with almost surely fully supported spaces and equal annealed sampled
matrices are equal, convergence of every annealed block to `L k` and leaf-tightness
give weak convergence to a law with annealed blocks `L k` and full support. -/
theorem leafTightFamily_of_uniqueness
    (huniq : ∀ Q Q' : ProbabilityMeasure MeasuredGHSpace.{u},
      (∀ k, annealedDistanceLaw Q k = annealedDistanceLaw Q' k) →
      (∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X) →
      (∀ᵐ X ∂(Q' : Measure MeasuredGHSpace.{u}), HasFullSupport X) → Q = Q')
    (P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u})
    (L : ∀ k : ℕ, ProbabilityMeasure (Fin k → Fin k → ℝ))
    (hM : ∀ k : ℕ, Tendsto (fun n ↦ annealedDistanceLaw (P n) k) atTop (𝓝 (L k)))
    (hleaf : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0)) :
    ∃ Q : ProbabilityMeasure MeasuredGHSpace.{u}, Tendsto P atTop (𝓝 Q) ∧
      (∀ k : ℕ, annealedDistanceLaw Q k = L k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X := by
  have htight := isTightMeasureSet_of_leafTight hM hleaf
  have hcomp : IsCompact (closure (range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext μ
    simp
  have hlimit {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Q : ProbabilityMeasure MeasuredGHSpace.{u}}
      (hQ : Tendsto (P ∘ φ) atTop (𝓝 Q)) :
      (∀ k, annealedDistanceLaw Q k = L k) ∧
        ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X :=
    ⟨annealedDistanceLaw_eq_of_tendsto_comp hM hφ hQ,
      ae_hasFullSupport_of_tendsto Q fun _ hδ ↦
        tendsto_annealedCoverRadius_of_tendsto_comp hleaf hφ hQ hδ⟩
  obtain ⟨Q₀, -, φ₀, hφ₀, hQ₀⟩ := hcomp.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  obtain ⟨hQ₀M, hQ₀S⟩ := hlimit hφ₀.tendsto_atTop hQ₀
  refine ⟨Q₀, ?_, hQ₀M, hQ₀S⟩
  apply tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨Q₁, -, φ₁, hφ₁, hQ₁⟩ :=
    hcomp.tendsto_subseq fun n ↦ subset_closure (mem_range_self (ψ n))
  obtain ⟨hQ₁M, hQ₁S⟩ := hlimit (hψ.comp hφ₁.tendsto_atTop) hQ₁
  refine ⟨φ₁, ?_⟩
  rw [huniq Q₀ Q₁ (fun k ↦ (hQ₀M k).trans (hQ₁M k).symm) hQ₀S hQ₁S]
  exact hQ₁

/-- **Proposition `C.1`, assuming identification of laws.** If two laws with
almost surely fully supported spaces and equal annealed sampled matrices are
equal, the leaf-tightness criterion holds. -/
theorem leafTightCriterion_of_uniqueness
    (huniq : ∀ Q Q' : ProbabilityMeasure MeasuredGHSpace.{u},
      (∀ k, annealedDistanceLaw Q k = annealedDistanceLaw Q' k) →
      (∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X) →
      (∀ᵐ X ∂(Q' : Measure MeasuredGHSpace.{u}), HasFullSupport X) → Q = Q') :
    LeafTightCriterion.{u} :=
  fun P M hM hleaf ↦ leafTightFamily_of_uniqueness huniq P (matrixBlockLaw M) hM hleaf

end Freezing2.MeasuredGHSpace
