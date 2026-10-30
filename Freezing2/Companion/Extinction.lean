module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.Path
public import Mathlib.Data.ENat.Lattice

/-!
# First extinction time

The stopping time is the first zero of the integer walk, or infinity if it
never hits zero. The value at time zero is one, so this agrees with the
paper's infimum over strictly positive indices. The walk itself is not stopped.
-/

@[expose] public section

namespace Freezing1

/-- First zero of `S`, or infinity if there is none (equation `eq:defintro`). -/
noncomputable def extinctionTime (x : SignSequence) : ℕ∞ :=
  open Classical in
  if h : ∃ k, activeCount x k = 0 then (Nat.find h : ℕ∞) else ⊤

/-- A nearest-neighbour walk starting at one stays positive until its first zero. -/
theorem positiveThrough_iff_no_zero (x : SignSequence) (n : ℕ) :
    PositiveThrough x n ↔ ∀ k ≤ n, activeCount x k ≠ 0 := by
  constructor
  · intro h k hk
    exact (h k hk).ne'
  · intro h
    induction n with
    | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
    | succ n ih =>
      have hn : PositiveThrough x n := ih (fun k hk => h k (by omega))
      intro k hk
      by_cases hkn : k ≤ n
      · exact hn k hkn
      · have hks : k = n + 1 := by omega
        subst k
        have hprev := hn n le_rfl
        have hnext := h (n + 1) le_rfl
        rw [activeCount_succ] at hnext ⊢
        cases hx : x (n + 1)
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
          omega
        · simp only [↓reduceIte]
          omega

theorem extinctionTime_le_iff (x : SignSequence) (n : ℕ) :
    extinctionTime x ≤ n ↔ ∃ k ≤ n, activeCount x k = 0 := by
  classical
  unfold extinctionTime
  split_ifs with h
  · simp only [ENat.natCast_le_natCast]
    constructor
    · intro hn
      exact ⟨Nat.find h, hn, Nat.find_spec h⟩
    · rintro ⟨k, hkn, hk⟩
      exact (Nat.find_min' h hk).trans hkn
  · simp only [top_le_iff, ENat.natCast_ne_top, false_iff]
    rintro ⟨k, hk, hz⟩
    exact h ⟨k, hz⟩

/-- Exact bridge between the paper's `τ > n` and `PositiveThrough`. -/
theorem lt_extinctionTime_iff (x : SignSequence) (n : ℕ) :
    (n : ℕ∞) < extinctionTime x ↔ PositiveThrough x n := by
  rw [← not_le, extinctionTime_le_iff, positiveThrough_iff_no_zero]
  push Not
  rfl

theorem extinctionTime_eq_top_iff (x : SignSequence) :
    extinctionTime x = ⊤ ↔ ∀ n, 0 < activeCount x n := by
  constructor
  · intro h n
    have hn : (n : ℕ∞) < extinctionTime x := by simp [h]
    exact ((lt_extinctionTime_iff x n).mp hn) n le_rfl
  · intro h
    unfold extinctionTime
    split_ifs with hz
    · obtain ⟨n, hn⟩ := hz
      exact False.elim ((h n).ne' hn)
    · rfl

/-- The walk is nonnegative through the extinction endpoint. -/
theorem activeCount_nonneg_of_le_extinctionTime {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) : 0 ≤ activeCount x n := by
  cases n with
  | zero => simp
  | succ n =>
    have hlt : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have hpos := ((lt_extinctionTime_iff x n).mp hlt) n le_rfl
    rw [activeCount_succ]
    cases x (n + 1) <;> simp_all <;> omega

end Freezing1
