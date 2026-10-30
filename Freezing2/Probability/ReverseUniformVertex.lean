module

public import Freezing2.Probability.ReversePaper

/-!
# Uniform birth times in the constructed reverse tree

The source's one-based labels are sampled uniformly conditional on the actual
terminal reverse tree. Its deterministic vertex set makes the unconditional
label law equal to the paper-facing uniform finite-set law.
-/

@[expose] public section

open MeasureTheory

namespace Freezing2.ReverseHistory

/-- Uniform sampling from the actual terminal reverse tree, with labels
transported to the manuscript's frozen integers and active one-based indices. -/
noncomputable def sourceUniformVertexLaw (x : ℕ → ℤ) (n : ℕ) : Measure VertexLabel :=
  (Freezing1.Reverse.uniformVertexLaw (companionSchedule x) n).map fromCompanionLabel

/-- The terminal forest used for uniform sampling is the terminal coordinate
of the concrete joint history. -/
theorem jointLaw_terminal_marginal (x : ℕ → ℤ) (n : ℕ) :
    (jointLaw (companionSchedule x) n).map (forestAt n 0) =
      Freezing1.Reverse.treeLaw (companionSchedule x) n := by
  change (jointLaw (companionSchedule x) n).map (fun ω ↦ ω n) = _
  exact jointLaw_map_eval (companionSchedule x) n n

theorem sourceUniformVertexLaw_eq (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hzero : ∀ k < n, activeCount x k ≠ 0) :
    sourceUniformVertexLaw x n = uniformVertex x n := by
  rw [sourceUniformVertexLaw, Freezing1.Reverse.uniformVertexLaw_eq _ _
    ((companion_le_extinctionTime_iff_no_zero_before x hx n).mpr hzero)]
  exact map_companion_uniformVertex x hx n

/-- N03 (`lem:bunif`) under the actual conditional uniform sampling law,
including the extinction endpoint. The result also covers `m=0`. -/
theorem sourceUniformVertexLaw_birth_lt (x : ℕ → ℤ) (hx : IsSigned x) {m n : ℕ}
    (hzero : ∀ k < n, activeCount x k ≠ 0) (hmn : m ≤ n) :
    (sourceUniformVertexLaw x n).real {v | birthTime n v < m} =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [sourceUniformVertexLaw_eq x hx hzero]
  exact uniformVertex_birth_lt_before_extinction x hx hmn hzero

end Freezing2.ReverseHistory
