module

public import Freezing2.Probability.ForwardHistoryLaw

/-!
# Recovering the complete forward history from the terminal tree

An attachment choice is recorded permanently as the new vertex's parent.
A freezing choice is recorded permanently by its freezing timestamp. The
terminal state therefore determines every legal history, for a fixed schedule
and horizon. This verifies the forward uniqueness step in the proof of N01.
-/

@[expose] public section

namespace Freezing2.ForwardHistory

/-- The active vertex chosen at the indicated (one-based) time. Values outside
`1,...,h.length` are unused by the reconstruction theorem. -/
def choiceAt : History → ℕ → ℕ
  | [], _ => 0
  | v :: h, t => if t = h.length + 1 then v else choiceAt h t

/-- Every nonempty frozen label in a constructed state is attached to a present
vertex and records a time already performed. -/
theorem frozenAt_mem_time (x : Freezing1.SignSequence) (h : History) {v t : ℕ}
    (ht : (state x h).frozenAt v = some t) :
    v ∈ (state x h).vertices ∧ 1 ≤ t ∧ t ≤ h.length := by
  induction h with
  | nil => simp [state, Freezing1.Forward.initial] at ht
  | cons w h ih =>
    by_cases hw : w ∈ (state x h).active
    · cases hx : x (h.length + 1) with
      | true =>
        by_cases hv : v = h.length + 1
        · simp [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.attach, hv] at ht
        · have ht' : (state x h).frozenAt v = some t := by
            simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.attach, hv] using ht
          obtain ⟨hm, hp, hb⟩ := ih ht'
          refine ⟨?_, hp, by simpa only [List.length_cons] using Nat.le_succ_of_le hb⟩
          simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.attach] using
            Finset.mem_insert_of_mem (b := h.length + 1) hm
      | false =>
        by_cases hv : v = w
        · have hte : h.length + 1 = t := by
            simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze, hv] using ht
          refine ⟨?_, by omega, by simp only [List.length_cons]; omega⟩
          simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze, hv] using
            (state_valid x h).active_subset hw
        · have ht' : (state x h).frozenAt v = some t := by
            simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze, hv] using ht
          obtain ⟨hm, hp, hb⟩ := ih ht'
          refine ⟨?_, hp, by simpa only [List.length_cons] using Nat.le_succ_of_le hb⟩
          simpa [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze] using hm
    · have ht' : (state x h).frozenAt v = some t := by
        simpa [state, Freezing1.Forward.step, hw] using ht
      obtain ⟨hm, hp, hb⟩ := ih ht'
      refine ⟨?_, hp, by simpa only [List.length_cons] using Nat.le_succ_of_le hb⟩
      simpa [state, Freezing1.Forward.step, hw] using hm

theorem frozenAt_new_vertex (x : Freezing1.SignSequence) (h : History) :
    (state x h).frozenAt (h.length + 1) = none := by
  cases he : (state x h).frozenAt (h.length + 1) with
  | none => rfl
  | some t =>
    have hm := (frozenAt_mem_time x h he).1
    have hb := (state_valid x h).vertices_le _ hm
    omega

/-- Earlier freezing labels persist through every later legal step. -/
theorem frozenAt_cons_past_iff (x : Freezing1.SignSequence) {h : History} {w v t : ℕ}
    (hw : w ∈ (state x h).active) (ht : t ≤ h.length) :
    (state x (w :: h)).frozenAt v = some t ↔ (state x h).frozenAt v = some t := by
  cases hx : x (h.length + 1) with
  | true =>
    by_cases hv : v = h.length + 1
    · simp [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.attach, hv,
        frozenAt_new_vertex]
    · simp [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.attach, hv]
  | false =>
    by_cases hv : v = w
    · have hn := ((state_valid x h).active_iff w
        ((state_valid x h).active_subset hw)).mp hw
      have hne : h.length + 1 ≠ t := by omega
      simp [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze, hv, hn, hne]
    · simp [state, Freezing1.Forward.step, hw, hx, Freezing1.Forward.freeze, hv]

/-- Every up-step choice can be read from the terminal parent map. -/
theorem parent_eq_choiceAt (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) {t : ℕ} (ht0 : 1 ≤ t) (ht : t ≤ h.length)
    (hx : x t = true) : (state x h).parent t = choiceAt h t := by
  induction h with
  | nil => simp at ht; omega
  | cons v h ih =>
    by_cases hte : t = h.length + 1
    · subst t
      simp [state, Freezing1.Forward.step, hh.2, hx, Freezing1.Forward.attach, choiceAt]
    · have htle : t ≤ h.length := by simp only [List.length_cons] at ht; omega
      have hi := ih hh.1 htle
      cases hxn : x (h.length + 1) <;>
        simpa [state, Freezing1.Forward.step, hh.2, hxn, Freezing1.Forward.attach,
          Freezing1.Forward.freeze, choiceAt, hte] using hi

/-- Every down-step choice is the unique vertex with that terminal frozen
label. This includes the last freezing step at extinction. -/
theorem frozenAt_eq_some_iff_choiceAt (x : Freezing1.SignSequence) {h : History}
    (hh : Legal x h) {t v : ℕ} (ht0 : 1 ≤ t) (ht : t ≤ h.length)
    (hx : x t = false) : (state x h).frozenAt v = some t ↔ choiceAt h t = v := by
  induction h with
  | nil => simp at ht; omega
  | cons w h ih =>
    by_cases hte : t = h.length + 1
    · subst t
      have hnot : (state x h).frozenAt v ≠ some (h.length + 1) := by
        intro he
        have hb := (frozenAt_mem_time x h he).2.2
        omega
      by_cases hv : v = w
      · simp [state, Freezing1.Forward.step, hh.2, hx, Freezing1.Forward.freeze,
          choiceAt, hv]
      · simp [state, Freezing1.Forward.step, hh.2, hx, Freezing1.Forward.freeze,
          choiceAt, hv, Ne.symm hv, hnot]
    · have htle : t ≤ h.length := by simp only [List.length_cons] at ht; omega
      rw [frozenAt_cons_past_iff x hh.2 htle]
      simpa only [choiceAt, ite_eq_right hte] using ih hh.1 htle

/-- Equal observations of all performed choices determine the entire history. -/
theorem eq_of_choiceAt_eq {h k : History} (hlen : h.length = k.length)
    (hc : ∀ t, 1 ≤ t → t ≤ h.length → choiceAt h t = choiceAt k t) : h = k := by
  induction h generalizing k with
  | nil => exact (List.length_eq_zero_iff.mp (by simpa using hlen.symm)).symm
  | cons v h ih =>
    cases k with
    | nil => simp at hlen
    | cons w k =>
      have hlen' : h.length = k.length := by simpa using hlen
      have hvw : v = w := by
        have he := hc (h.length + 1) (by omega) (by simp)
        simpa [choiceAt, hlen'] using he
      have hhk : h = k := ih hlen' (by
        intro t ht0 ht
        have he := hc t ht0 (by simpa only [List.length_cons] using Nat.le_succ_of_le ht)
        have hne : t ≠ h.length + 1 := by omega
        simpa [choiceAt, ← hlen', hne] using he)
      simp [hvw, hhk]

/-- The source's forward history uniqueness statement, with the schedule and
horizon support restriction explicit. No reverse-law premise is used. -/
theorem state_injective_on_legal (x : Freezing1.SignSequence) {h k : History}
    (hh : Legal x h) (hk : Legal x k) (hlen : h.length = k.length)
    (he : state x h = state x k) : h = k := by
  apply eq_of_choiceAt_eq hlen
  intro t ht0 ht
  have htk : t ≤ k.length := hlen ▸ ht
  cases hx : x t with
  | true =>
    rw [← parent_eq_choiceAt x hh ht0 ht hx,
      ← parent_eq_choiceAt x hk ht0 htk hx, he]
  | false =>
    have hf : (state x h).frozenAt (choiceAt h t) = some t :=
      (frozenAt_eq_some_iff_choiceAt x hh ht0 ht hx).mpr rfl
    rw [he] at hf
    exact ((frozenAt_eq_some_iff_choiceAt x hk ht0 htk hx).mp hf).symm

end Freezing2.ForwardHistory
