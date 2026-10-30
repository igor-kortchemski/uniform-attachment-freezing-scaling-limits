module

public import Freezing2.Probability.ForwardHistorySupport
public import Freezing2.Probability.ForwardHistoryUnique

/-!
# Exact masses of schedule-compatible terminal forward trees

The source history product is the probability of each actual terminal state
that can arise from the fixed schedule. This support restriction is essential:
aggregate counts alone do not identify the permitted edge and frozen labels.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Freezing2.ForwardHistory

/-- Every sampled terminal tree admits a legal history for the actual fixed
schedule, including a final freezing step at extinction. -/
theorem treeLaw_ae_exists_legal_history (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ s ∂Freezing1.Forward.treeLaw x n,
      ∃ h : History, h.length = n ∧ Legal x h ∧ state x h = s := by
  rw [← map_law_state, ae_map_iff measurable_from_top.aemeasurable (by trivial)]
  filter_upwards [law_length x n, law_legal x n hn] with h hlen hh
  exact ⟨h, hlen, hh, rfl⟩

/-- The terminal-state atom has exactly the mass of its unique legal history. -/
theorem treeLaw_singleton_eq_history (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) (hn : (h.length : ℕ∞) ≤ Freezing1.extinctionTime x) :
    Freezing1.Forward.treeLaw x h.length {state x h} = law x h.length {h} := by
  rw [← map_law_state, Measure.map_apply measurable_from_top (by trivial)]
  apply measure_congr
  filter_upwards [law_length x h.length, law_legal x h.length hn] with k hlen hk
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  apply propext
  constructor
  · intro he
    exact state_injective_on_legal x hk hh hlen he
  · rintro rfl
    rfl

/-- The precise support-corrected forward probability formula in the counting
proof of N01. The right-hand side is the paper's product over `1/S_(i-1)`. -/
theorem treeLaw_real_singleton_of_legal (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) (hn : (h.length : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (Freezing1.Forward.treeLaw x h.length).real {state x h} =
      Freezing1.forwardHistoryWeight x h.length := by
  change (Freezing1.Forward.treeLaw x h.length {state x h}).toReal = _
  rw [treeLaw_singleton_eq_history x hh hn]
  exact law_real_singleton_of_legal x hh hn

/-- Trees without a legal history for the given schedule have zero mass. -/
theorem treeLaw_singleton_eq_zero_of_not_reachable (x : Freezing1.SignSequence)
    (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (s : Freezing1.Forward.State)
    (hs : ¬∃ h : History, h.length = n ∧ Legal x h ∧ state x h = s) :
    Freezing1.Forward.treeLaw x n {s} = 0 := by
  apply measure_mono_null _ (ae_iff.mp (treeLaw_ae_exists_legal_history x n hn))
  simpa only [Set.singleton_subset_iff, Set.mem_ofPred_eq] using hs

end Freezing2.ForwardHistory
