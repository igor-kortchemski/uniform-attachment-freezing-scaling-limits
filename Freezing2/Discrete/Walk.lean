module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Tactic

/-!
# The deterministic driving walk

The paper's walk is indexed by positive integers and starts at one.  The identities
below are the exact counting part of equation `eq:pn` (the proof of Lemma
`lem:hnalpha`) and the combinatorial denominator in Lemma `lem:bunif`.
No asymptotic or probabilistic conclusion is assumed or asserted here.
-/

@[expose] public section

namespace Freezing2

/-- The driving sequence takes its values in `{−1, 1}` at positive times. -/
def IsSigned (x : ℕ → ℤ) : Prop := ∀ i, 0 < i → x i = 1 ∨ x i = -1

/-- The walk `Sₙ = 1 + ∑ᵢ₌₁ⁿ Xᵢ`, before imposing any survival condition. -/
def activeCount (x : ℕ → ℤ) (n : ℕ) : ℤ := 1 + ∑ i ∈ Finset.Ioc 0 n, x i

/-- The attachment times in the half-open interval `(a,b]`. -/
def upSteps (x : ℕ → ℤ) (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter (fun i => x i = 1)

/-- The freezing times in the half-open interval `(a,b]`. -/
def downSteps (x : ℕ → ℤ) (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter (fun i => x i = -1)

@[simp] theorem activeCount_zero (x : ℕ → ℤ) : activeCount x 0 = 1 := by
  simp [activeCount]

/-- Reading one sign changes the active count by that sign. -/
theorem activeCount_succ (x : ℕ → ℤ) (n : ℕ) :
    activeCount x (n + 1) = activeCount x n + x (n + 1) := by
  simp only [activeCount, Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  omega

/-- The signs in an interval add up to the difference of the endpoint heights. -/
theorem sum_steps (x : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ioc a b, x i = activeCount x b - activeCount x a := by
  have h := Finset.sum_Ioc_consecutive x (Nat.zero_le a) hab
  simp only [activeCount]
  omega

/-- Finite signed summation, with no positivity assumption on the running walk. -/
theorem sum_signed (x : ℕ → ℤ) (s : Finset ℕ)
    (hx : ∀ i ∈ s, x i = 1 ∨ x i = -1) :
    ∑ i ∈ s, x i = ((s.filter (fun i => x i = 1)).card : ℤ) -
      ((s.filter (fun i => x i = -1)).card : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi' := hx i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, x j = 1 ∨ x j = -1 :=
      fun j hj => hx j (Finset.mem_insert_of_mem hj)
    rcases hi' with h | h
    · simp [h, Finset.sum_insert hi, Finset.filter_insert, hi, ih hs]
      omega
    · simp [h, Finset.sum_insert hi, Finset.filter_insert, hi, ih hs]
      omega

/-- Every positive time is exactly one of an attachment and a freezing time. -/
theorem upSteps_card_add_downSteps_card (x : ℕ → ℤ) (hx : IsSigned x)
    {a b : ℕ} :
    (upSteps x a b).card + (downSteps x a b).card = b - a := by
  have heq : (Finset.Ioc a b).filter (fun i => ¬ x i = 1) = downSteps x a b := by
    ext i
    simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hi, hxi⟩
      exact ⟨hi, (hx i (lt_of_le_of_lt (Nat.zero_le a) hi.1)).resolve_left hxi⟩
    · rintro ⟨hi, hxi⟩
      exact ⟨hi, by omega⟩
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioc a b)
    (p := fun i => x i = 1)
  rw [heq] at h
  simpa [upSteps] using h

/-- The difference between the numbers of up and down steps is `S_b - S_a`. -/
theorem upSteps_card_sub_downSteps_card (x : ℕ → ℤ) (hx : IsSigned x)
    {a b : ℕ} (hab : a ≤ b) :
    ((upSteps x a b).card : ℤ) - ((downSteps x a b).card : ℤ) =
      activeCount x b - activeCount x a := by
  rw [← sum_steps x hab]
  exact (sum_signed x (Finset.Ioc a b) (fun i hi =>
    hx i (lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_Ioc.mp hi).1))).symm

/-- Exact up-step identity in equation `eq:pn`, before its asymptotic specialization. -/
theorem twice_upSteps_card (x : ℕ → ℤ) (hx : IsSigned x)
    {a b : ℕ} (hab : a ≤ b) :
    2 * ((upSteps x a b).card : ℤ) =
      (b : ℤ) - (a : ℤ) + activeCount x b - activeCount x a := by
  have hsum := upSteps_card_add_downSteps_card x hx (a := a) (b := b)
  have hdiff := upSteps_card_sub_downSteps_card x hx hab
  omega

/-- Exact down-step identity, used in counting vertices with early birth times. -/
theorem twice_downSteps_card (x : ℕ → ℤ) (hx : IsSigned x)
    {a b : ℕ} (hab : a ≤ b) :
    2 * ((downSteps x a b).card : ℤ) =
      (b : ℤ) - (a : ℤ) - activeCount x b + activeCount x a := by
  have hsum := upSteps_card_add_downSteps_card x hx (a := a) (b := b)
  have hdiff := upSteps_card_sub_downSteps_card x hx hab
  omega

/-- Number of frozen vertices at time `n`, in doubled integer form. -/
theorem twice_frozen_count (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    2 * ((downSteps x 0 n).card : ℤ) = (n : ℤ) + 1 - activeCount x n := by
  have h := twice_downSteps_card x hx (Nat.zero_le n)
  simp only [Nat.cast_zero, sub_zero, activeCount_zero] at h
  omega

/-- Each attachment creates one vertex, in addition to the initial root. -/
theorem twice_vertex_count (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    2 * (((upSteps x 0 n).card : ℤ) + 1) = (n : ℤ) + 1 + activeCount x n := by
  have h := twice_upSteps_card x hx (Nat.zero_le n)
  simp only [Nat.cast_zero, sub_zero, activeCount_zero] at h
  omega

/-- Up to every time under consideration, there is still an active vertex. -/
def SurvivesThrough (x : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ k, k ≤ n → 0 < activeCount x k

/-- Survival implies the current active count is a genuine positive natural number. -/
theorem activeCount_toNat_pos (x : ℕ → ℤ) {n : ℕ} (h : SurvivesThrough x n) :
    0 < (activeCount x n).toNat := by
  have hn := h n le_rfl
  omega

/-- The number of vertices equals frozen labels plus active labels. -/
theorem frozen_add_active_eq_vertex_count (x : ℕ → ℤ) (hx : IsSigned x)
    {n : ℕ} (h : 0 ≤ activeCount x n) :
    (downSteps x 0 n).card + (activeCount x n).toNat = (upSteps x 0 n).card + 1 := by
  have hdiff := upSteps_card_sub_downSteps_card x hx (Nat.zero_le n)
  have hcast := Int.toNat_of_nonneg h
  simp only [activeCount_zero] at hdiff
  omega

/-- Before the first zero of a signed walk started at one, its value is positive. -/
theorem activeCount_pos_of_no_zero (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ)
    (hzero : ∀ k, k ≤ n → activeCount x k ≠ 0) : 0 < activeCount x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun k hk => hzero k (by omega))
    have hne := hzero (n + 1) le_rfl
    have hstep := activeCount_succ x n
    rcases hx (n + 1) (by omega) with h | h <;> omega

/-- At or before the first zero, the active count is nonnegative. -/
theorem activeCount_nonneg_of_no_zero_before (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ)
    (hzero : ∀ k, k < n → activeCount x k ≠ 0) : 0 ≤ activeCount x n := by
  cases n with
  | zero => simp
  | succ n =>
    have hn := activeCount_pos_of_no_zero x hx n (fun k hk => hzero k (by omega))
    have hstep := activeCount_succ x n
    rcases hx (n + 1) (by omega) with h | h <;> omega

/-- Casting a surviving walk to naturals preserves the walk exactly. -/
theorem activeCount_nat_cast (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i ≤ N) :
    ((activeCount x i).toNat : ℤ) = activeCount x i :=
  Int.toNat_of_nonneg (le_of_lt (hs i hi))

/-- A surviving signed walk gives a natural-number walk with unit up or down steps. -/
theorem activeCount_nat_steps (x : ℕ → ℤ) (hx : IsSigned x) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i < N) :
    (activeCount x (i + 1)).toNat = (activeCount x i).toNat + 1 ∨
      (activeCount x i).toNat = (activeCount x (i + 1)).toNat + 1 := by
  have h₀ := activeCount_nat_cast x hs (Nat.le_of_lt hi)
  have h₁ := activeCount_nat_cast x hs (by omega : i + 1 ≤ N)
  have hstep := activeCount_succ x i
  rcases hx (i + 1) (by omega) with h | h <;> omega

/-- Up steps in the natural representation are exactly the original `+1` signs. -/
theorem activeCount_nat_up_iff (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i < N) :
    (activeCount x (i + 1)).toNat = (activeCount x i).toNat + 1 ↔ x (i + 1) = 1 := by
  have h₀ := activeCount_nat_cast x hs (Nat.le_of_lt hi)
  have h₁ := activeCount_nat_cast x hs (by omega : i + 1 ≤ N)
  have hstep := activeCount_succ x i
  omega

/-- Down steps in the natural representation are exactly the original `−1` signs. -/
theorem activeCount_nat_down_iff (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i < N) :
    (activeCount x i).toNat = (activeCount x (i + 1)).toNat + 1 ↔ x (i + 1) = -1 := by
  have h₀ := activeCount_nat_cast x hs (Nat.le_of_lt hi)
  have h₁ := activeCount_nat_cast x hs (by omega : i + 1 ≤ N)
  have hstep := activeCount_succ x i
  omega

/-- A surviving natural walk stays strictly positive at all available times. -/
theorem activeCount_nat_pos (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i ≤ N) : 0 < (activeCount x i).toNat := by
  have h := hs i hi
  omega

end Freezing2
