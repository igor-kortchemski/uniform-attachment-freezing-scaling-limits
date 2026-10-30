module

public import Freezing2.Probability.OldestBlock
public import Freezing2.Analysis.TightnessBlockArithmetic

/-!
# One-block critical nonmerger bound

The actual reverse-process version of N14 with a nonnegative target phase.
The oldest-vertex comparison, component recurrence, signed-step count,
ceiling arithmetic, and final numerical coefficient are proved dependencies.
The invalid source block index zero is not silently given a forest value.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.TrackedClusters

open Freezing1

/-- The exact `3 M sqrt(k)/(4K)` bound under finite sufficient conditions.
The source block has length `4 ceil(M n/sqrt(k))`; its target phase is `t`.
All `K+1` marked vertices are present at its initial phase, and `u` is oldest. -/
theorem one_step_tightness {x : SignSequence} {n k K t : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : 0 < k) (hkn : k ≤ n) (hK : 0 < K)
    {M : ℝ} (hM : 0 < M) (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ s ≤ n, (Freezing1.activeCount x s : ℝ) ≤ M * Real.sqrt n)
    (hblock : t + tightnessBlockLength M n k ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    (hcard : A.card = K + 1) {u : ℕ ⊕ ℕ} (hu : u ∈ A)
    (holdest : ∀ v ∈ A, Freezing1.birthTime n v ≤ Freezing1.birthTime n u)
    (hborn : ∀ v ∈ A, t + tightnessBlockLength M n k ≤ Freezing1.birthTime n v) :
    (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} ≤
      3 * M * Real.sqrt k / (4 * K) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  have hB : 0 < M * Real.sqrt n := mul_pos hM (Real.sqrt_pos.mpr hnr)
  have hgap := tightnessBlockLength_gap hM hk hkn
  have ha : 0 < M * Real.sqrt k := by linarith
  have hm : M * Real.sqrt n < (tightnessBlockLength M n k : ℝ) := by
    by_contra h
    have hp := mul_nonpos_of_nonneg_of_nonpos ha.le
      (sub_nonpos.mpr (le_of_not_gt h))
    nlinarith [sq_pos_of_pos hB]
  have hb := oldest_isolation_probability_le_block_bound hn hblock hA hu holdest hborn
    hB hpop hm
  rw [hcard, Nat.cast_add, Nat.cast_one] at hb
  have hnum := one_block_isolation_numeric_bound hB hlarge hgap hK
  simpa only [mul_assoc] using hb.trans hnum

/-- N14 for actual positive source block indices. The source's oldest and
middle-block birth assumptions imply all premises of the finite theorem. -/
theorem one_step_tightness_positive_block {x : SignSequence} {n k K i : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : 0 < k) (hkn : k ≤ n) (hK : 0 < K)
    {M : ℝ} (hM : 0 < M) (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ s ≤ n, (Freezing1.activeCount x s : ℝ) ≤ M * Real.sqrt n)
    (hi : 1 ≤ i) (hin : i * tightnessBlockLength M n k ≤ n)
    {v : Fin (K + 1) → ℕ ⊕ ℕ} (hvinj : Function.Injective v)
    (hv : ∀ j, v j ∈ Freezing1.vertexLabels x n)
    (hborn0 : (i + 1) * tightnessBlockLength M n k < Freezing1.birthTime n (v 0))
    (hborn : ∀ j : Fin (K + 1), j ≠ 0 →
      i * tightnessBlockLength M n k < Freezing1.birthTime n (v j) ∧
      Freezing1.birthTime n (v j) ≤ (i + 1) * tightnessBlockLength M n k) :
    (Reverse.lawAfter x n (n - (i - 1) * tightnessBlockLength M n k)).real
      {F | Alone F (Finset.univ.image v) (v 0)} ≤
        3 * M * Real.sqrt k / (4 * K) := by
  have he : (i - 1) * tightnessBlockLength M n k + tightnessBlockLength M n k =
      i * tightnessBlockLength M n k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hi]
  have hinc : i * tightnessBlockLength M n k ≤ (i + 1) * tightnessBlockLength M n k :=
    Nat.mul_le_mul_right _ (Nat.le_succ i)
  apply one_step_tightness hn hk hkn hK hM hlarge hpop
    (by simpa only [he] using hin)
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact hv j
  · rw [Finset.card_image_of_injective _ hvinj, Finset.card_univ, Fintype.card_fin]
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    by_cases hj : j = 0
    · subst j
      exact le_rfl
    · exact (hborn j hj).2.trans hborn0.le
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    rw [he]
    by_cases hj : j = 0
    · subst j
      exact hinc.trans hborn0.le
    · exact (hborn j hj).1.le

end Freezing2.TrackedClusters
