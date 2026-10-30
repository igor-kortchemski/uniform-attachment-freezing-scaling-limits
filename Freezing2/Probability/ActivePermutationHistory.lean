module

public import Freezing2.Probability.ActiveLabelPermutation
public import Freezing2.Probability.ReverseChoiceHistory

/-!
# The active-label action on actual reverse choice histories

Attachment pairs are relabelled and deterministic freezing placeholders are
kept unchanged. The exact stamped state commutes with this action, which
preserves legal support. Consequently the factorial terminal forest orbit
consists of actual legal outputs, not merely abstract compatible structures.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.ReverseStamped

theorem activeLabelEquiv_mem_phaseLabels (x : Freezing1.SignSequence) (n i : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) (v : ℕ ⊕ ℕ) :
    activeLabelEquiv σ v ∈ Freezing1.Reverse.phaseLabels x n i ↔
      v ∈ Freezing1.Reverse.phaseLabels x n i := by
  cases v with
  | inl j =>
    by_cases hj : j < (Freezing1.activeCount x n).toNat
    · rw [show activeLabelEquiv σ (Sum.inl j) = Sum.inl (σ ⟨j, hj⟩).val from
        activeLabelEquiv_active σ ⟨j, hj⟩]
      simp [Freezing1.Reverse.phaseLabels, hj, (σ ⟨j, hj⟩).isLt]
    · rw [activeLabelEquiv_inactive σ (Nat.le_of_not_lt hj)]
  | inr j => rw [activeLabelEquiv_frozen]

theorem activeLabelEquiv_map_phaseLabels (x : Freezing1.SignSequence) (n i : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) :
    (Freezing1.Reverse.phaseLabels x n i).map (activeLabelEquiv σ).toEmbedding =
      Freezing1.Reverse.phaseLabels x n i := by
  ext v
  rw [Finset.mem_map_equiv, activeLabelEquiv_symm]
  exact activeLabelEquiv_mem_phaseLabels x n i σ.symm v

theorem relabelActive_initial (x : Freezing1.SignSequence) (n : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) :
    relabelActive σ (Freezing1.ReverseStamped.initial x n) =
      Freezing1.ReverseStamped.initial x n := by
  apply stampedForest_ext
  · apply rootedForest_ext
    · change ((Finset.range (Freezing1.activeCount x n).toNat).disjSum ∅).map
          (activeLabelEquiv σ).toEmbedding =
        (Finset.range (Freezing1.activeCount x n).toNat).disjSum ∅
      rw [← Freezing1.Reverse.phaseLabels_top x n]
      exact activeLabelEquiv_map_phaseLabels x n n σ
    · funext v
      exact (activeLabelEquiv σ).apply_symm_apply v
    · funext v
      exact (activeLabelEquiv σ).apply_symm_apply v
    · rfl
  · rfl

noncomputable def permuteChoice {m : ℕ} (σ : Equiv.Perm (Fin m)) (p : ReverseChoiceHistory.Choice) :
    ReverseChoiceHistory.Choice := (activeLabelEquiv σ p.1, activeLabelEquiv σ p.2)

/-- Only genuine attachment choices are permuted. Freezing entries are a fixed
recording convention, so their placeholder is retained. -/
noncomputable def permuteHistory (x : Freezing1.SignSequence) (n : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) :
    ReverseChoiceHistory.History → ReverseChoiceHistory.History
  | [] => []
  | p :: h => (if x (n - (h.length + 1) + 1) then permuteChoice σ p else p) ::
      permuteHistory x n σ h

@[simp] theorem permuteHistory_length (x : Freezing1.SignSequence) (n : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat))
    (h : ReverseChoiceHistory.History) : (permuteHistory x n σ h).length = h.length := by
  induction h <;> simp [permuteHistory, *]

theorem relabelActive_step {m : ℕ} (σ : Equiv.Perm (Fin m))
    (x : Freezing1.SignSequence) (i : ℕ) (F : Forest) (p : ReverseChoiceHistory.Choice) :
    relabelActive σ (ReverseChoiceHistory.step x i F p) =
      ReverseChoiceHistory.step x i (relabelActive σ F)
        (if x (i + 1) then permuteChoice σ p else p) := by
  cases hx : x (i + 1)
  · simp only [ReverseChoiceHistory.step, hx, Bool.false_eq_true, ite_false, relabelActive]
    exact relabel_insertLabel _ F i (activeLabelEquiv_frozen σ i)
  · simp only [ReverseChoiceHistory.step, hx, ite_true, relabelActive, permuteChoice]
    exact relabel_joinChoice _ F (i + 1) p

theorem state_permuteHistory (x : Freezing1.SignSequence) (n : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat))
    (h : ReverseChoiceHistory.History) :
    ReverseChoiceHistory.state x n (permuteHistory x n σ h) =
      relabelActive σ (ReverseChoiceHistory.state x n h) := by
  induction h with
  | nil => exact (relabelActive_initial x n σ).symm
  | cons p h ih =>
    simp only [permuteHistory, ReverseChoiceHistory.state, permuteHistory_length]
    rw [ih, ← relabelActive_step]

theorem legal_permuteHistory (x : Freezing1.SignSequence) (n : ℕ)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat))
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h) :
    ReverseChoiceHistory.Legal x n (permuteHistory x n σ h) := by
  induction h with
  | nil => trivial
  | cons p h ih =>
    simp only [permuteHistory, ReverseChoiceHistory.Legal, permuteHistory_length,
      state_permuteHistory]
    refine ⟨ih hh.1, hh.2.1, ?_⟩
    cases hx : x (n - (h.length + 1) + 1)
    · simpa [hx] using hh.2.2
    · have hp : p ∈ (ReverseChoiceHistory.state x n h).forest.roots.offDiag := by
        simpa [hx] using hh.2.2
      simpa [hx, permuteChoice, relabelActive, relabel_roots, Finset.mem_offDiag] using hp

@[simp] theorem permuteHistory_refl (x : Freezing1.SignSequence) (n : ℕ)
    (h : ReverseChoiceHistory.History) :
    permuteHistory x n (Equiv.refl _) h = h := by
  induction h <;> simp [permuteHistory, permuteChoice, *]

theorem permuteHistory_trans (x : Freezing1.SignSequence) (n : ℕ)
    (σ τ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat))
    (h : ReverseChoiceHistory.History) :
    permuteHistory x n τ (permuteHistory x n σ h) = permuteHistory x n (σ.trans τ) h := by
  induction h with
  | nil => rfl
  | cons p h ih =>
    simp only [permuteHistory, permuteHistory_length, ih]
    split_ifs <;> simp [permuteChoice, ← activeLabelEquiv_trans, Equiv.trans_apply]

/-- Every element of the factorial forest orbit is an actual legal output of
the same terminal horizon, with exactly the original history length. -/
theorem activeOrbit_supported_by_legal_histories (x : Freezing1.SignSequence) (n : ℕ)
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h)
    {F : Forest} (hF : F ∈ activeOrbit (Freezing1.activeCount x n).toNat
      (ReverseChoiceHistory.state x n h)) :
    ∃ h' : ReverseChoiceHistory.History, ReverseChoiceHistory.Legal x n h' ∧
      h'.length = h.length ∧ ReverseChoiceHistory.state x n h' = F := by
  obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp hF
  exact ⟨permuteHistory x n σ h, legal_permuteHistory x n σ hh,
    permuteHistory_length x n σ h, (state_permuteHistory x n σ h).trans hσ⟩

end Freezing2.ReverseStamped
