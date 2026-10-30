module

public import Freezing2.Probability.ReverseChoiceSupport
public import Freezing2.Probability.ReverseChoiceUnique

/-!
# Exact masses of labelled terminal reverse trees

The stamped reverse terminal forest determines its unique ordered-root history.
Consequently every permitted labelled terminal tree has the source reverse
history mass. Erasing the distinct active labels requires a separate fibre
bijection and is not asserted by this module.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Freezing2.ReverseChoiceHistory

theorem treeLaw_ae_exists_legal_history (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n,
      ∃ h : History, h.length = n ∧ Legal x n h ∧ state x n h = F := by
  change ∀ᵐ F ∂Freezing1.ReverseStamped.lawAfter x n n, _
  rw [← map_law_state x n n le_rfl,
    ae_map_iff measurable_from_top.aemeasurable (by trivial)]
  filter_upwards [law_length x n n, law_legal x n n hn le_rfl] with h hlen hh
  exact ⟨h, hlen, hh, rfl⟩

/-- Exact equality of the actual terminal-tree atom and its uniquely
reconstructed history atom, retaining all active labels. -/
theorem treeLaw_singleton_eq_history (x : Freezing1.SignSequence) (n : ℕ)
    {h : History} (hh : Legal x n h) (hlen : h.length = n)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    Freezing1.ReverseStamped.treeLaw x n {state x n h} = law x n n {h} := by
  change Freezing1.ReverseStamped.lawAfter x n n {state x n h} = _
  rw [← map_law_state x n n le_rfl, Measure.map_apply measurable_from_top (by trivial)]
  apply measure_congr
  filter_upwards [law_length x n n, law_legal x n n hn le_rfl] with k hlenk hk
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  apply propext
  constructor
  · intro he
    exact state_injective_on_legal x n hk hh hn (hlenk.trans hlen.symm) he
  · rintro rfl
    rfl

/-- The actual labelled terminal atom equals the paper's reverse product
of `1/(S_i*(S_i-1))` over attachment indices. -/
theorem treeLaw_real_singleton_of_legal (x : Freezing1.SignSequence) (n : ℕ)
    {h : History} (hh : Legal x n h) (hlen : h.length = n)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (Freezing1.ReverseStamped.treeLaw x n).real {state x n h} =
      Freezing1.reverseHistoryWeight x n := by
  change (Freezing1.ReverseStamped.treeLaw x n {state x n h}).toReal = _
  rw [treeLaw_singleton_eq_history x n hh hlen hn]
  exact law_terminal_real_singleton_of_legal x n hh hlen hn

theorem treeLaw_singleton_eq_zero_of_not_reachable (x : Freezing1.SignSequence)
    (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (F : Forest)
    (hF : ¬∃ h : History, h.length = n ∧ Legal x n h ∧ state x n h = F) :
    Freezing1.ReverseStamped.treeLaw x n {F} = 0 := by
  apply measure_mono_null _ (ae_iff.mp (treeLaw_ae_exists_legal_history x n hn))
  simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hF

end Freezing2.ReverseChoiceHistory
