module

public import Freezing2.Probability.HeightApproximation

/-!
# Exact harmonic decomposition for the noncritical distance limits

The inclusive coalescence comparison is the absolute difference of the two
root-prefix lengths plus the common part below their minimum birth. All
endpoint terms, including time zero and the diagonal, are retained.
-/

@[expose] public section

open scoped BigOperators

namespace Freezing2

theorem harmonicInterval_eq_sum_Ioc (x : ℕ → ℤ) (a b : ℕ) :
    harmonicInterval x a (b - a) =
      ∑ i ∈ Finset.Ioc a b, (activeCount x i : ℝ)⁻¹ := by
  exact (sum_Ioc_eq_sum_range_offset (fun i ↦ (activeCount x i : ℝ)⁻¹) a b).symm

/-- Consecutive half-open intervals concatenate without an endpoint correction. -/
theorem harmonicInterval_consecutive (x : ℕ → ℤ) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    harmonicInterval x a (b - a) + harmonicInterval x b (c - b) =
      harmonicInterval x a (c - a) := by
  simp only [harmonicInterval_eq_sum_Ioc]
  exact Finset.sum_Ioc_consecutive _ hab hbc

theorem harmonicInterval_prefix_difference (x : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    harmonicInterval x 0 b - harmonicInterval x 0 a = harmonicInterval x a (b - a) := by
  have h := harmonicInterval_consecutive x (Nat.zero_le a) hab
  simp only [Nat.sub_zero] at h
  linarith

theorem harmonicInterval_nonneg (x : ℕ → ℤ) {N a b : ℕ}
    (hs : SurvivesThrough x N) (hb : b ≤ N) : 0 ≤ harmonicInterval x a (b - a) := by
  rw [harmonicInterval_eq_sum_Ioc]
  apply Finset.sum_nonneg
  intro i hi
  have hpos : (0 : ℝ) < activeCount x i := by
    exact_mod_cast hs i ((Finset.mem_Ioc.mp hi).2.trans hb)
  exact inv_nonneg.mpr hpos.le

/-- Splitting an inclusive interval retains its shared endpoint only once. -/
theorem inclusiveHarmonic_split (x : ℕ → ℤ) {c a b : ℕ} (hca : c ≤ a) (hab : a ≤ b) :
    inclusiveHarmonic x c b = inclusiveHarmonic x c a + harmonicInterval x a (b - a) := by
  rw [inclusiveHarmonic_eq x (hca.trans hab), inclusiveHarmonic_eq x hca,
    ← harmonicInterval_consecutive x hca hab]
  ring

theorem harmonic_coalescence_decomposition_of_le (x : ℕ → ℤ) {N c a b : ℕ}
    (hs : SurvivesThrough x N) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ N) :
    inclusiveHarmonic x c a / 2 + inclusiveHarmonic x c b / 2 =
      |harmonicInterval x 0 a / 2 - harmonicInterval x 0 b / 2| +
        inclusiveHarmonic x c a := by
  have hp := harmonicInterval_prefix_difference x hab
  have hnonneg := harmonicInterval_nonneg x hs (a := a) hb
  rw [abs_of_nonpos (by linarith :
    harmonicInterval x 0 a / 2 - harmonicInterval x 0 b / 2 ≤ 0),
    inclusiveHarmonic_split x hca hab]
  linarith

/-- The exact decomposition used in the subcritical distance-matrix proof,
valid for arbitrary vertex birth order and also on the diagonal. -/
theorem harmonic_coalescence_decomposition (x : ℕ → ℤ) {N c a b : ℕ}
    (hs : SurvivesThrough x N) (hca : c ≤ a) (hcb : c ≤ b)
    (ha : a ≤ N) (hb : b ≤ N) :
    inclusiveHarmonic x c a / 2 + inclusiveHarmonic x c b / 2 =
      |harmonicInterval x 0 a / 2 - harmonicInterval x 0 b / 2| +
        inclusiveHarmonic x c (min a b) := by
  rcases le_total a b with hab | hba
  · simpa only [min_eq_left hab] using
      harmonic_coalescence_decomposition_of_le x hs hca hab hb
  · simpa only [min_eq_right hba, abs_sub_comm, add_comm] using
      harmonic_coalescence_decomposition_of_le x hs hcb hba ha

end Freezing2
