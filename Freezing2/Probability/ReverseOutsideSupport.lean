module

public import Freezing2.Probability.ReverseChoiceHistory

/-!
# Normal form outside the actual reverse vertex set

The forest representation has total parent, root, depth and timestamp fields.
Actual reverse states keep identity parent/root and zero depth/time at labels
that are absent. This fact is necessary when a canonical observation is used
to reconstruct the full represented forest, rather than only its present part.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseStamped

def OutsideNormal (F : Forest) : Prop := ∀ v ∉ F.forest.vertices,
  F.forest.parent v = v ∧ F.forest.root v = v ∧ F.forest.depth v = 0 ∧ F.edgeTime v = 0

theorem initial_outsideNormal (x : Freezing1.SignSequence) (n : ℕ) :
    OutsideNormal (Freezing1.ReverseStamped.initial x n) := by
  intro v _
  simp [Freezing1.ReverseStamped.initial, Freezing1.Reverse.initial,
    Freezing1.RootedForest.isolated]

theorem OutsideNormal.joinChoice {F : Forest} (hF : OutsideNormal F) (t : ℕ)
    (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    OutsideNormal (Freezing1.ReverseStamped.joinChoice F t p) := by
  by_cases hp : p ∈ F.forest.roots.offDiag
  · intro v hv
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp] at hv ⊢
    change v ∉ F.forest.vertices at hv
    have hvb : v ≠ p.2 := fun he ↦ hv (he ▸
      (Freezing1.RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).2.1).1)
    obtain ⟨hparent, hroot, hdepth, htime⟩ := hF v hv
    simp [Freezing1.RootedForest.join, hvb, hparent, hroot, hdepth, htime]
  · simpa [Freezing1.ReverseStamped.joinChoice, hp] using hF

theorem OutsideNormal.insertLabel {F : Forest} (hF : OutsideNormal F) (i : ℕ) :
    OutsideNormal (Freezing1.ReverseStamped.insertLabel F i) := by
  by_cases hi : Sum.inr i ∈ F.forest.vertices
  · simpa [Freezing1.ReverseStamped.insertLabel, hi] using hF
  · intro v hv
    simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_right hi,
      Freezing1.RootedForest.adjoin_vertices, Finset.mem_insert, not_or] at hv ⊢
    obtain ⟨hparent, hroot, hdepth, htime⟩ := hF v hv.2
    simp [Freezing1.RootedForest.adjoin, hv.1, hparent, hroot, hdepth, htime]

/-- The full total-field invariant holds for every legal deterministic history,
without requiring a separately assumed law identity. -/
theorem state_outsideNormal_of_legal (x : Freezing1.SignSequence) (n : ℕ)
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h) :
    OutsideNormal (ReverseChoiceHistory.state x n h) := by
  induction h with
  | nil => exact initial_outsideNormal x n
  | cons p h ih =>
    simp only [ReverseChoiceHistory.state, ReverseChoiceHistory.step]
    split_ifs
    · exact (ih hh.1).joinChoice _ _
    · exact (ih hh.1).insertLabel _

/-- Even the total-kernel fallback preserves the outside normal form. -/
theorem transitionLaw_outsideNormal (x : Freezing1.SignSequence) (i : ℕ)
    {F : Forest} (hF : OutsideNormal F) :
    ∀ᵐ G ∂Freezing1.ReverseStamped.transitionLaw x i F, OutsideNormal G := by
  cases hx : x (i + 1)
  · simp only [Freezing1.ReverseStamped.transitionLaw, hx, Bool.false_eq_true, ite_false]
    exact (ae_dirac_iff (by trivial)).mpr (hF.insertLabel i)
  · simp only [Freezing1.ReverseStamped.transitionLaw, hx, ite_true]
    by_cases htwo : 2 ≤ F.forest.roots.card
    · exact Freezing1.ReverseStamped.joinLaw_ae F (i + 1) htwo OutsideNormal
        (fun p _ ↦ hF.joinChoice (i + 1) p)
    · simpa only [Freezing1.ReverseStamped.joinLaw, ite_eq_right htwo] using
        (show ∀ᵐ G ∂Measure.dirac F, OutsideNormal G from
          (ae_dirac_iff (by trivial)).mpr hF)

theorem lawAfter_outsideNormal (x : Freezing1.SignSequence) (n k : ℕ) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.lawAfter x n k, OutsideNormal F := by
  induction k with
  | zero => simpa [Freezing1.ReverseStamped.lawAfter] using initial_outsideNormal x n
  | succ k ih =>
    by_cases hk : k < n
    · apply (ae_iff_prob_eq_one measurable_from_top).mpr
      rw [Freezing1.ReverseStamped.lawAfter, ite_eq_left hk,
        Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
      calc
        _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂Freezing1.ReverseStamped.lawAfter x n k := by
          apply lintegral_congr_ae
          filter_upwards [ih] with F hF
          exact (ae_iff_prob_eq_one measurable_from_top).mp
            (transitionLaw_outsideNormal x (n - (k + 1)) hF)
        _ = 1 := by simp
    · simpa only [Freezing1.ReverseStamped.lawAfter, ite_eq_right hk] using ih

theorem treeLaw_outsideNormal (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n, OutsideNormal F :=
  lawAfter_outsideNormal x n n

end Freezing2.ReverseStamped
