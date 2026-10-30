module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.Extinction
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The product identity comparing forward and reverse histories

The last displayed identity in the proof of `thm:samelaw` is a deterministic
identity of the schedule. This module checks the induction stated there,
including the extinction endpoint. Identifying the products with probabilities
of actual tree histories is a separate obligation.
-/

@[expose] public section

namespace Freezing1

open scoped BigOperators

/-- If the next step is permitted, the walk is positive through the current
time, even when that next step is the extinction step. -/
theorem positiveThrough_of_succ_le_extinctionTime {x : SignSequence} {n : ℕ}
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x) : PositiveThrough x n := by
  apply (lt_extinctionTime_iff x n).mp
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn

/-- A forward attachment creates at least two active vertices. Hence the
corresponding reverse step has a nonempty set of ordered pairs of roots. -/
theorem two_le_activeCount_succ_of_attachment {x : SignSequence} {n : ℕ}
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x) (hx : x (n + 1) = true) :
    2 ≤ activeCount x (n + 1) := by
  have hp := positiveThrough_of_succ_le_extinctionTime hn n le_rfl
  rw [activeCount_succ, hx]
  simp only [↓reduceIte]
  omega

theorem two_le_activeCount_toNat_succ_of_attachment {x : SignSequence} {n : ℕ}
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ extinctionTime x) (hx : x (n + 1) = true) :
    2 ≤ (activeCount x (n + 1)).toNat := by
  have hp := two_le_activeCount_succ_of_attachment hn hx
  omega

/-- Product of the reciprocal active counts immediately before each step. -/
noncomputable def forwardHistoryWeight (x : SignSequence) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (activeCount x i : ℝ)⁻¹

/-- Product of the uniform ordered-pair factors at reverse coalescence steps.
Freezing steps contribute one, as they insert a prescribed singleton. -/
noncomputable def reverseHistoryWeight (x : SignSequence) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    if x (i + 1) then
      ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1))⁻¹
    else 1

@[simp] theorem forwardHistoryWeight_zero (x : SignSequence) :
    forwardHistoryWeight x 0 = 1 := by simp [forwardHistoryWeight]

@[simp] theorem reverseHistoryWeight_zero (x : SignSequence) :
    reverseHistoryWeight x 0 = 1 := by simp [reverseHistoryWeight]

theorem forwardHistoryWeight_succ (x : SignSequence) (n : ℕ) :
    forwardHistoryWeight x (n + 1) =
      forwardHistoryWeight x n * (activeCount x n : ℝ)⁻¹ := by
  simp only [forwardHistoryWeight, Finset.prod_range_succ]

theorem reverseHistoryWeight_succ (x : SignSequence) (n : ℕ) :
    reverseHistoryWeight x (n + 1) = reverseHistoryWeight x n *
      if x (n + 1) then
        ((activeCount x (n + 1) : ℝ) * ((activeCount x (n + 1) : ℝ) - 1))⁻¹
      else 1 := by
  simp [reverseHistoryWeight, Finset.prod_range_succ]

private theorem real_toNat_of_nonneg {a : ℤ} (ha : 0 ≤ a) :
    (a.toNat : ℝ) = (a : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg ha

private theorem factorial_toNat_succ {a : ℤ} (ha : 0 ≤ a) :
    (((a + 1).toNat).factorial : ℝ) = ((a : ℝ) + 1) * (a.toNat.factorial : ℝ) := by
  have heq : (a + 1).toNat = a.toNat + 1 := by omega
  rw [heq, Nat.factorial_succ]
  push_cast
  rw [real_toNat_of_nonneg ha]

/-- The factorial correction exactly relates the two history products.
This includes `n = τ`, where `S_n = 0` and `0! = 1`. -/
theorem reverseHistoryWeight_eq_factorial_inv_mul_forward
    (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    reverseHistoryWeight x n =
      (Nat.factorial (activeCount x n).toNat : ℝ)⁻¹ * forwardHistoryWeight x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have hpos : 0 < activeCount x n :=
      ((lt_extinctionTime_iff x n).mp hlt) n le_rfl
    have hnonneg := activeCount_nonneg_of_le_extinctionTime hn
    rw [reverseHistoryWeight_succ, forwardHistoryWeight_succ, ih hlt.le]
    cases hx : x (n + 1)
    · have hnext : activeCount x (n + 1) = activeCount x n - 1 := by
        rw [activeCount_succ, hx]
        simp [sub_eq_add_neg]
      have hprev : activeCount x n = activeCount x (n + 1) + 1 := by omega
      have hf := factorial_toNat_succ hnonneg
      rw [← hprev] at hf
      have hr : (activeCount x (n + 1) : ℝ) + 1 = (activeCount x n : ℝ) := by
        exact_mod_cast hprev.symm
      rw [hr] at hf
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      rw [hf, mul_inv_rev]
      ring
    · have hnext : activeCount x (n + 1) = activeCount x n + 1 := by
        rw [activeCount_succ, hx]
        simp
      have hf := factorial_toNat_succ hpos.le
      rw [← hnext] at hf
      have hr : (activeCount x (n + 1) : ℝ) = (activeCount x n : ℝ) + 1 := by
        exact_mod_cast hnext
      simp only [↓reduceIte]
      rw [hf, hr]
      simp only [add_sub_cancel_right, mul_inv_rev]
      ring

/-- Every forward history factor is strictly positive up to and including
extinction: the denominator belongs to the time before the current step. -/
theorem forwardHistoryWeight_pos (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : 0 < forwardHistoryWeight x n := by
  unfold forwardHistoryWeight
  apply Finset.prod_pos
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hiτ : (i : ℕ∞) < extinctionTime x :=
    lt_of_lt_of_le (by exact_mod_cast hin) hn
  have hpos := ((lt_extinctionTime_iff x i).mp hiτ) i le_rfl
  exact inv_pos.mpr (by exact_mod_cast hpos)

/-- Relabelling the active vertices has exactly the factorial multiplicity
needed to cancel the reverse-history normalization. This is the scalar identity
only; a bijection between labelled tree fibres is not asserted here. -/
theorem factorial_mul_reverseHistoryWeight_eq_forward
    (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (Nat.factorial (activeCount x n).toNat : ℝ) * reverseHistoryWeight x n =
      forwardHistoryWeight x n := by
  rw [reverseHistoryWeight_eq_factorial_inv_mul_forward x n hn, ← mul_assoc]
  have hf : (Nat.factorial (activeCount x n).toNat : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (activeCount x n).toNat
  rw [mul_inv_cancel₀ hf, one_mul]

theorem reverseHistoryWeight_pos (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : 0 < reverseHistoryWeight x n := by
  rw [reverseHistoryWeight_eq_factorial_inv_mul_forward x n hn]
  exact mul_pos (inv_pos.mpr (by positivity)) (forwardHistoryWeight_pos x n hn)

end Freezing1
