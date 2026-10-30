module

public import Freezing2.Probability.ReverseChoiceHistory

/-!
# Recovering the ordered-root history from a stamped terminal forest

A positive edge timestamp identifies the child root selected at that step;
the child's permanent parent identifies the first selected root. Later reverse
steps modify only roots, so they preserve all previously created parent edges.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.ReverseChoiceHistory

/-- Choice at the one-based reverse step. -/
def choiceAt : History → ℕ → Choice
  | [], _ => noChoice
  | p :: h, j => if j = h.length + 1 then p else choiceAt h j

/-- Freezing phases have exactly one recorded choice. -/
theorem choiceAt_freezing (x : Freezing1.SignSequence) (n : ℕ) {h : History}
    (hh : Legal x n h) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ h.length)
    (hx : x (n - j + 1) = false) : choiceAt h j = noChoice := by
  induction h with
  | nil => simp at hj; omega
  | cons p h ih =>
    by_cases he : j = h.length + 1
    · subst j
      simpa [choiceAt, hx] using hh.2.2
    · have hj' : j ≤ h.length := by simp only [List.length_cons] at hj; omega
      simpa only [choiceAt, ite_eq_right he] using ih hh.1 hj'

/-- The terminal timestamp and parent permanently record both selected roots
of each earlier positive step. -/
theorem choiceAt_attachment_recorded (x : Freezing1.SignSequence) (n : ℕ)
    {h : History} (hh : Legal x n h) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ h.length) (hx : x (n - j + 1) = true) :
    (choiceAt h j).2 ∈ (state x n h).forest.vertices ∧
      (state x n h).edgeTime (choiceAt h j).2 = n - j + 1 ∧
      (state x n h).forest.parent (choiceAt h j).2 = (choiceAt h j).1 := by
  induction h with
  | nil => simp at hj; omega
  | cons p h ih =>
    have hvalid := state_valid_of_legal x n hh.1 hn
    by_cases he : j = h.length + 1
    · subst j
      have hp : p ∈ (state x n h).forest.roots.offDiag := by simpa [hx] using hh.2.2
      have hmem := (Freezing1.RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).2.1).1
      simpa [state, step, hx, choiceAt, Freezing1.ReverseStamped.joinChoice, hp,
        Freezing1.RootedForest.join] using hmem
    · have hj' : j ≤ h.length := by simp only [List.length_cons] at hj; omega
      obtain ⟨hmem, htime, hparent⟩ := ih hh.1 hj'
      have ht0 : n - j + 1 ≠ 0 := by omega
      have hnonroot : (choiceAt h j).2 ∉ (state x n h).forest.roots := by
        intro hr
        have hz := (hvalid.2.root_zero _ hmem).mpr hr
        rw [htime] at hz
        exact ht0 hz
      cases hxn : x (n - (h.length + 1) + 1) with
      | true =>
        have hp : p ∈ (state x n h).forest.roots.offDiag := by simpa [hxn] using hh.2.2
        have hne : (choiceAt h j).2 ≠ p.2 := by
          intro heq
          exact hnonroot (heq.symm ▸ (Finset.mem_offDiag.mp hp).2.1)
        simpa [state, step, hxn, choiceAt, he, Freezing1.ReverseStamped.joinChoice, hp,
          Freezing1.RootedForest.join, hne] using ⟨hmem, htime, hparent⟩
      | false =>
        have hfresh : Sum.inr (n - (h.length + 1)) ∉ (state x n h).forest.vertices := by
          rw [hvalid.1.vertices_eq]
          have hphase : n - h.length = n - (h.length + 1) + 1 := by have := hh.2.1; omega
          rw [hphase]
          exact Freezing1.Reverse.fresh_freezing_label x n _
        have hne : (choiceAt h j).2 ≠ Sum.inr (n - (h.length + 1)) := by
          intro heq
          exact hfresh (heq ▸ hmem)
        simp only [state, step, hxn, Bool.false_eq_true, ite_false, choiceAt,
          ite_eq_right he, Freezing1.ReverseStamped.insertLabel, dite_eq_right hfresh,
          Freezing1.RootedForest.adjoin, Function.update_of_ne hne, hne]
        exact ⟨Finset.mem_insert_of_mem hmem, htime, hparent⟩

theorem eq_of_choiceAt_eq {h k : History} (hlen : h.length = k.length)
    (hc : ∀ j, 1 ≤ j → j ≤ h.length → choiceAt h j = choiceAt k j) : h = k := by
  induction h generalizing k with
  | nil => exact (List.length_eq_zero_iff.mp (by simpa using hlen.symm)).symm
  | cons p h ih =>
    cases k with
    | nil => simp at hlen
    | cons q k =>
      have hlen' : h.length = k.length := by simpa using hlen
      have hpq : p = q := by
        have he := hc (h.length + 1) (by omega) (by simp)
        simpa [choiceAt, hlen'] using he
      have hhk : h = k := ih hlen' (by
        intro j hj0 hj
        have he := hc j hj0 (by simpa only [List.length_cons] using Nat.le_succ_of_le hj)
        have hne : j ≠ h.length + 1 := by omega
        simpa [choiceAt, ← hlen', hne] using he)
      simp [hpq, hhk]

/-- Every complete labelled stamped reverse forest has at most one legal
ordered-root history. Active-label erasure is a separate finite-fibre step. -/
theorem state_injective_on_legal (x : Freezing1.SignSequence) (n : ℕ)
    {h k : History} (hh : Legal x n h) (hk : Legal x n k)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hlen : h.length = k.length)
    (he : state x n h = state x n k) : h = k := by
  apply eq_of_choiceAt_eq hlen
  intro j hj0 hj
  have hjk : j ≤ k.length := hlen ▸ hj
  cases hx : x (n - j + 1) with
  | false => rw [choiceAt_freezing x n hh hj0 hj hx, choiceAt_freezing x n hk hj0 hjk hx]
  | true =>
    obtain ⟨hmem, htime, hparent⟩ := choiceAt_attachment_recorded x n hh hn hj0 hj hx
    obtain ⟨kmem, ktime, kparent⟩ := choiceAt_attachment_recorded x n hk hn hj0 hjk hx
    rw [← he] at kmem ktime kparent
    have ht0 : n - j + 1 ≠ 0 := by omega
    have hchild : (choiceAt h j).2 = (choiceAt k j).2 :=
      (state_valid_of_legal x n hh hn).2.injective _ hmem _ kmem
        (by rw [htime]; exact ht0) (by rw [ktime]; exact ht0) (htime.trans ktime.symm)
    have hfst : (choiceAt h j).1 = (choiceAt k j).1 := by
      rw [hchild] at hparent
      exact hparent.symm.trans kparent
    exact Prod.ext hfst hchild

end Freezing2.ReverseChoiceHistory
