module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.Path
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound on the height scale

This proves the lemma labelled `lemme minoration h_n^+` in the paper. The
proof uses the count of preceding attachment steps directly: at the `k`-th
attachment, the active population is at most `k + 1`. This gives the same
harmonic lower bound as the paper's adjacent-transposition argument, without
constructing the transpositions. The transposition argument itself is not
formalized here.
-/

@[expose] public section

namespace Freezing1

/-- The deterministic height scale `h_n^+` from the Introduction. -/
noncomputable def heightScale (x : SignSequence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0

/-- The shifted harmonic sum `1/2 + 1/3 + … + 1/(n+1)`. -/
noncomputable def shiftedHarmonic (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2)

@[simp] theorem heightScale_zero (x : SignSequence) : heightScale x 0 = 0 := by
  simp [heightScale]

theorem heightScale_succ (x : SignSequence) (n : ℕ) :
    heightScale x (n + 1) = heightScale x n +
      if x (n + 1) then 1 / (activeCount x (n + 1) : ℝ) else 0 := by
  simp [heightScale, Finset.sum_range_succ]

@[simp] theorem shiftedHarmonic_zero : shiftedHarmonic 0 = 0 := by
  simp [shiftedHarmonic]

theorem shiftedHarmonic_succ (n : ℕ) :
    shiftedHarmonic (n + 1) = shiftedHarmonic n + 1 / ((n : ℝ) + 2) := by
  simp [shiftedHarmonic, Finset.sum_range_succ]

/-- The harmonic lower bound in the proof of the paper's lower-bound lemma. -/
theorem shiftedHarmonic_le_heightScale {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) : shiftedHarmonic (plusCount x n) ≤ heightScale x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (h.mono (Nat.le_succ n))
    rw [plusCount_succ, heightScale_succ]
    cases hx : x (n + 1)
    · simpa [hx] using ih'
    · simp only [↓reduceIte, shiftedHarmonic_succ]
      apply add_le_add ih'
      have hpos : 0 < (activeCount x (n + 1) : ℝ) := by
        exact_mod_cast h (n + 1) le_rfl
      have hbound : (activeCount x (n + 1) : ℝ) ≤ (plusCount x n : ℝ) + 2 := by
        have hi := activeCount_le_plusCount_add_one x (n + 1)
        simp [hx] at hi
        exact_mod_cast hi
      exact one_div_le_one_div_of_le hpos hbound

/-- An elementary logarithmic lower bound for the shifted harmonic sum. -/
theorem log_le_shiftedHarmonic (n : ℕ) :
    Real.log (((n : ℝ) + 2) / 2) ≤ shiftedHarmonic n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hn' : 0 < (n : ℝ) + 3 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn' hn)
    have hr : ((n : ℝ) + 3) / ((n : ℝ) + 2) - 1 = 1 / ((n : ℝ) + 2) := by
      field_simp
      ring
    rw [hr, Real.log_div hn'.ne' hn.ne'] at hlog
    rw [shiftedHarmonic_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.log_div (by positivity) (by norm_num)] at ih ⊢
    have heq : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
    rw [heq]
    linarith

/-- A stronger intermediate form of the lower bound, in terms of attachments. -/
theorem log_plusCount_le_heightScale {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) :
    Real.log (((plusCount x n : ℝ) + 2) / 2) ≤ heightScale x n :=
  (log_le_shiftedHarmonic _).trans (shiftedHarmonic_le_heightScale h)

/-- The normalization used in the height theorems is strictly positive. -/
theorem heightScale_pos {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (h : PositiveThrough x n) : 0 < heightScale x n := by
  have hc : 1 ≤ plusCount x n := by
    have := le_two_mul_plusCount h
    omega
  have hc' : (1 : ℝ) ≤ plusCount x n := by exact_mod_cast hc
  have hlog : 0 < Real.log (((plusCount x n : ℝ) + 2) / 2) := by
    apply Real.log_pos
    linarith
  exact hlog.trans_le (log_plusCount_le_heightScale h)

/-- Paper lemma `lemme minoration h_n^+`: `h_n^+ ≥ log(n/4)` before extinction. -/
theorem log_quarter_le_heightScale {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (h : PositiveThrough x n) :
    Real.log ((n : ℝ) / 4) ≤ heightScale x n := by
  have hn' : 0 < (n : ℝ) / 4 := by positivity
  have hcount : (n : ℝ) ≤ 2 * (plusCount x n : ℝ) := by
    exact_mod_cast le_two_mul_plusCount h
  apply (Real.log_le_log hn' ?_).trans (log_plusCount_le_heightScale h)
  linarith

/-- The height scale diverges for every admissible triangular array of schedules.
This is the deterministic input to the proof of Theorem `thm:height` (I). -/
theorem tendsto_heightScale_atTop (x : ℕ → SignSequence)
    (h : ∀ n, PositiveThrough (x n) n) :
    Filter.Tendsto (fun n => heightScale (x n) n) Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop)
  apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hlog
  exact (Filter.eventually_ge_atTop 1).mono fun n hn =>
    log_quarter_le_heightScale hn (h n)

end Freezing1
