module

public import Freezing2.Probability.ForwardReplay

/-!
# Vertices and edges of a legal forward replay

The replay contains precisely the schedule's birth identifiers, and its edges
are precisely the prescribed attachment-parent edges. These statements connect
the record-based canonical map with the source's actual tree geometry.
-/

@[expose] public section

namespace Freezing2.ForwardReplay

/-- A legal replay has exactly the schedule's birth identifiers. -/
theorem vertices_history (x : Freezing1.SignSequence) (parent fv : ℕ → ℕ)
    (k : ℕ) (hk : ForwardHistory.Legal x (history x parent fv k)) (v : ℕ) :
    v ∈ (ForwardHistory.state x (history x parent fv k)).vertices ↔ Born x k v := by
  induction k with
  | zero =>
    simp [history, ForwardHistory.state, Freezing1.Forward.initial, Born]
    omega
  | succ k ih =>
    have hv := hk.2
    cases hx : x (k + 1) with
    | false =>
      simpa only [history, ForwardHistory.state, history_length, Freezing1.Forward.step,
        ite_eq_left hv, hx, Bool.false_eq_true, ite_false, Freezing1.Forward.freeze,
        born_succ, and_false, false_or] using ih hk.1
    | true =>
      simp only [history, ForwardHistory.state, history_length, Freezing1.Forward.step,
        ite_eq_left hv, hx, ite_true, Freezing1.Forward.attach, Finset.mem_insert,
        ih hk.1, born_succ, and_true]

/-- The actual graph contains exactly the edges added at positive schedule
indices, including all labels and the root-zero boundary convention. -/
theorem graph_adj_history (x : Freezing1.SignSequence) (parent fv : ℕ → ℕ)
    (k : ℕ) (hk : ForwardHistory.Legal x (history x parent fv k)) (u v : ℕ) :
    (ForwardHistory.state x (history x parent fv k)).graph.Adj u v ↔
      ∃ t, 1 ≤ t ∧ t ≤ k ∧ x t = true ∧ (SimpleGraph.edge (parent t) t).Adj u v := by
  induction k with
  | zero =>
    simp only [history, ForwardHistory.state, Freezing1.Forward.initial, SimpleGraph.bot_adj,
      false_iff, not_exists, not_and]
    omega
  | succ k ih =>
    have hv := hk.2
    cases hx : x (k + 1) with
    | false =>
      simp only [history, ForwardHistory.state, history_length, Freezing1.Forward.step,
        ite_eq_left hv, hx, Bool.false_eq_true, ite_false, Freezing1.Forward.freeze]
      rw [ih hk.1]
      constructor
      · rintro ⟨t, ht0, htk, hxt, he⟩
        exact ⟨t, ht0, by omega, hxt, he⟩
      · rintro ⟨t, ht0, htk, hxt, he⟩
        have hne : t ≠ k + 1 := by intro h; rw [h, hx] at hxt; contradiction
        exact ⟨t, ht0, by omega, hxt, he⟩
    | true =>
      simp only [history, ForwardHistory.state, history_length, Freezing1.Forward.step,
        ite_eq_left hv, hx, ite_true, Freezing1.Forward.attach, SimpleGraph.sup_adj]
      rw [ih hk.1]
      simp only [choice, hx, ite_true]
      constructor
      · rintro (⟨t, ht0, htk, hxt, he⟩ | he)
        · exact ⟨t, ht0, by omega, hxt, he⟩
        · exact ⟨k + 1, by omega, le_rfl, hx, he⟩
      · rintro ⟨t, ht0, htk, hxt, he⟩
        by_cases ht : t = k + 1
        · exact Or.inr (ht ▸ he)
        · exact Or.inl ⟨t, ht0, by omega, hxt, he⟩

end Freezing2.ForwardReplay
